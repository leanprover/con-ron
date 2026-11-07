//! `ConLeche/Frontend/Olean/Files.lean` — from the file system (task #142).
//!
//! Where a module's files are on the search path, and each of the reads.
//!
//! ## The seam: [`OleanFs`]
//!
//! Upstream's reads are actions of its `CheckerIO` class.  Here they go through
//! one trait in the idiom of `export_c::ChunkSource`, holding the operations of
//! the class the reader uses, **with `&self`**: an operation is a function of its
//! arguments, which is what upstream's model says of one snapshot of the files.
//! The extraction renders it as a typeclass whose fields are functions into
//! `Result`, so the extracted reader is quantified over an arbitrary instance;
//! the instance over `std` is in `crates/con-ron`, outside the theorems.
//!
//! ## Deviations
//!
//! * **The read's heartbeat is two operations of the seam**
//!   (`read_notes_say`, `read_notes_module_loaded`): upstream's `ReadNotes`
//!   (task #484) are `IO` state handed to `CheckerIO.liftIO`; here the notes,
//!   the pace and the clock are the instance's, built where the instance is
//!   (`crates/con-ron`'s `olean_fs`), not in `readOleans`.
//!
//! * **An operation's failure is a value**: `Result<_, Vec<u32>>`, the message.
//!   Upstream's `IO.Error` is an exception that `findModule` catches for its own
//!   reads and `runArgs` for the rest; here the rest is `.internal` with that
//!   message, exit 3 as well, the verdict line's shape the reader's.
//! * **Paths are `Vec<u32>`**, as every `String` of the core, and `System.FilePath`'s
//!   `/`, `addExtension` and `withFileName` are spelled out: [`path_join`],
//!   [`path_add_extension`].
//! * **`parseConstName` of a number past the word** saturates: no stored name has
//!   one (`spec::nat_word`), so the constant is not in the closure, exit 3 as
//!   upstream's.

use crate::arena::env;
use crate::arena::handle::NIdx;
use crate::arena::store::{EStore, PersTier};
use crate::frontend::olean::header;
use crate::frontend::olean::header::HdrWalk;
use crate::frontend::olean::module;
use crate::frontend::olean::module::Expo;
use crate::frontend::olean::region;
use crate::frontend::olean::region::Part;
use crate::frontend::olean::spec::{ImportRec, ModDecoded, OleanPins, RdErr};
use crate::frontend::olean::view;
use crate::frontend::olean::view::{AllViews, ModFiles, OLeanLevel};
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::expr;
use crate::kernel::name;
use crate::kernel::name::Name;

/// con-leche: ConLeche/Frontend/CheckerIO.lean:122-167 CheckerIO
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::OleanFs_refines, then delete this line
/// **The checker's file reads**: the operations of upstream's class the reader
/// uses, and the read's heartbeat, two of the `liftIO` actions upstream hands
/// the class.  A failure is the operation's message.  The class's worker map
/// (`parMapWorkers`) is the check pool's, in `crates/con-ron`.
pub trait OleanFs {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:122-167 CheckerIO
    /// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::path_exists_refines, then delete this line
    /// whether the path names something (a file, a directory)
    fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:122-167 CheckerIO
    /// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::real_path_refines, then delete this line
    /// the path with every symbolic link resolved, absolute
    fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:122-167 CheckerIO
    /// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::read_bin_file_refines, then delete this line
    /// a regular file's bytes
    fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:122-167 CheckerIO
    /// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::read_range_refines, then delete this line
    /// a positional read: the bytes from `off` up to `off + len` or the end of
    /// the file, whichever comes first
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:122-167 CheckerIO
    /// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::file_size_refines, then delete this line
    /// the size of a regular file in bytes
    fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:42-48 ReadNotes.say
    /// `CheckerIO.liftIO (n.say line)`: one line of the read's heartbeat, the
    /// instance's notes (module note).  Changes nothing a read returns.
    fn read_notes_say(&self, line: &Vec<u32>);
    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:50-60 ReadNotes.moduleLoaded
    /// `CheckerIO.liftIO (n.moduleLoaded total size)`: a module of `total` is
    /// loaded, with `size` constants.  Changes nothing a read returns.
    fn read_notes_module_loaded(&self, total: u64, size: u64);
}

/// con-leche: none — `System.FilePath`'s `/` (`join`): an absolute `sub` replaces
/// the path, as it does there.
pub fn path_join(p: &Vec<u32>, sub: &Vec<u32>) -> Vec<u32> {
    if sub.len() > 0 && sub[0] == 47 {
        expr::str_copy(sub)
    } else {
        let mut out = text::cat(expr::str_copy(p), &{ const M: [u32; 1] = [47]; crate::kernel::core_types::code_points(&M) });
        out = text::cat(out, sub);
        out
    }
}

/// con-leche: none — `System.FilePath.addExtension` with its `fileName` and
/// `withFileName`: `.ext` onto the last component, unless that is empty, `.` or
/// `..`, which is no file name; a direct child of the root keeps upstream's
/// spelling `//x.ext`.
pub fn path_add_extension(p: &Vec<u32>, ext: &Vec<u32>) -> Vec<u32> {
    let mut sep = p.len();
    let mut found = false;
    while sep > 0 && !found {
        sep -= 1;
        if p[sep] == 47 {
            found = true;
        }
    }
    let start = if found { sep + 1 } else { 0 };
    let n = p.len() - start;
    let is_dot = n == 1 && p[start] == 46;
    let is_dotdot = n == 2 && p[start] == 46 && p[start + 1] == 46;
    if n == 0 || is_dot || is_dotdot {
        return expr::str_copy(p);
    }
    let mut out: Vec<u32> = Vec::with_capacity(p.len() + ext.len() + 2);
    if found && sep == 0 {
        out.push(47);
    }
    let mut i = 0usize;
    while i < p.len() {
        out.push(p[i]);
        i += 1;
    }
    if ext.len() > 0 {
        out.push(46);
    }
    text::cat(out, ext)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:28-34 modFile.comps
/// con-leche: ConLeche/Frontend/Olean/Files.lean:28-34 modFile
/// The file a module's level is stored in.
pub fn mod_file(pers: &PersTier, ar: &EStore, dir: &Vec<u32>, m: &NIdx, ext: &Vec<u32>) -> Result<Vec<u32>, CheckError> {
    match env::read_name(pers, ar, m) {
        Err(e) => Err(e),
        Ok(n) => {
            let cs = name::component_list(&n, Vec::new());
            let mut path = expr::str_copy(dir);
            let mut k = cs.len();
            while k > 0 {
                k -= 1;
                let comp: Vec<u32> = match &cs[k] {
                    name::NameComponent::Str(s) => expr::str_copy(s),
                    name::NameComponent::Num(i) => text::u64_str(*i),
                };
                path = path_join(&path, &comp);
            }
            Ok(path_add_extension(&path, ext))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:36-38 NameScan
/// Where the scan of a name is.
pub enum NameScan {
    Start,
    Plain,
    Esc,
    Closed,
}

/// con-leche: none — `cur.all Char.isDigit`
pub fn all_digits(cur: &Vec<u32>) -> bool {
    let mut i = 0usize;
    while i < cur.len() {
        if cur[i] < 48 || cur[i] > 57 {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: none — `cur.toNat!` saturating (module note)
pub fn digits_value(cur: &Vec<u32>) -> u64 {
    let mut v = 0u64;
    let mut i = 0usize;
    while i < cur.len() {
        let d = (cur[i] - 48) as u64;
        if v > (u64::MAX - d) / 10 {
            return u64::MAX;
        }
        v = v * 10 + d;
        i += 1;
    }
    v
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:40-43 Name.pushPlain
/// A component as written without an escape: at `nums`, one of digits alone is a
/// number, as Lean's name literals read it.
pub fn name_push_plain(n: Name, cur: Vec<u32>, nums: bool) -> Name {
    if nums && cur.len() > 0 && all_digits(&cur) {
        name::mk_num(n, digits_value(&cur))
    } else {
        name::mk_str(n, cur)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:45-62 scanName
/// The scan of a name, one character at a time.
pub fn scan_name_go(nums: bool, s: &Vec<u32>) -> Option<(Name, NameScan, Vec<u32>)> {
    let mut n: Name = name::anonymous();
    let mut st = NameScan::Start;
    let mut cur: Vec<u32> = Vec::new();
    let mut i = 0usize;
    while i < s.len() {
        let c = s[i];
        match st {
            NameScan::Start => {
                if c == 171 {
                    st = NameScan::Esc;
                    cur = Vec::new();
                } else if c == 46 {
                    return None;
                } else {
                    cur = Vec::new();
                    cur.push(c);
                    st = NameScan::Plain;
                }
            }
            NameScan::Plain => {
                if c == 46 {
                    n = name_push_plain(n, core::mem::replace(&mut cur, Vec::new()), nums);
                    st = NameScan::Start;
                } else {
                    cur.push(c);
                    st = NameScan::Plain;
                }
            }
            NameScan::Esc => {
                if c == 187 {
                    if cur.len() == 0 {
                        return None;
                    }
                    n = name::mk_str(n, core::mem::replace(&mut cur, Vec::new()));
                    st = NameScan::Closed;
                } else {
                    cur.push(c);
                    st = NameScan::Esc;
                }
            }
            NameScan::Closed => {
                if c == 46 {
                    st = NameScan::Start;
                    cur = Vec::new();
                } else {
                    return None;
                }
            }
        }
        i += 1;
    }
    Some((n, st, cur))
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:45-62 scanName
/// The scan's end: where it stopped says whether that is a name.
pub fn scan_name(nums: bool, s: &Vec<u32>) -> Option<Name> {
    match scan_name_go(nums, s) {
        None => None,
        Some((n, st, cur)) => match st {
            NameScan::Plain => Some(name_push_plain(n, cur, nums)),
            NameScan::Closed => Some(n),
            _ => None,
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:64-70 parseModName
/// **A module name as the command line spells it**.
pub fn parse_mod_name(s: &Vec<u32>) -> Option<Name> {
    scan_name(false, s)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:72-75 parseConstName
/// **A constant's name as the command line spells it**.
pub fn parse_const_name(s: &Vec<u32>) -> Option<Name> {
    scan_name(true, s)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:77-82 Located
/// **Where a module's files are**.
pub struct Located {
    pub dir: Vec<u32>,
    pub has_server: bool,
    pub has_private: bool,
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:84-85 partExts
/// The three files of a module, by extension.
pub fn part_ext(i: usize) -> Vec<u32> {
    if i == 0 {
        { const M: [u32; 5] = [111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) }
    } else if i == 1 {
        { const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }
    } else {
        { const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:87-96 locateIn
/// One directory's answer: the real paths of the module's three files.
pub struct Hit {
    pub dir: Vec<u32>,
    pub files: Vec<Option<Vec<u32>>>,
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:139-160 findModule
/// How `locateHits` fails: the file system's message, or the store's readback.
pub enum LocErr {
    Fs(Vec<u32>),
    Err(CheckError),
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:87-96 locateIn
/// The real paths of a module's three files in one directory, `None` where absent.
pub fn locate_in<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, m: &NIdx, d: &Vec<u32>) -> Result<Hit, LocErr> {
    let mut files: Vec<Option<Vec<u32>>> = Vec::with_capacity(3);
    let mut i = 0usize;
    while i < 3 {
        match locate_file(fs, pers, ar, m, d, i) {
            Err(e) => return Err(e),
            Ok(x) => files.push(x),
        }
        i += 1;
    }
    Ok(Hit { dir: expr::str_copy(d), files })
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:87-96 locateIn
/// The real path of file `i`, `None` where absent.
pub fn locate_file<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, m: &NIdx, d: &Vec<u32>, i: usize) -> Result<Option<Vec<u32>>, LocErr> {
    match mod_file(pers, ar, d, m, &part_ext(i)) {
        Err(e) => Err(LocErr::Err(e)),
        Ok(p) => match fs.path_exists(&p) {
            Err(e) => Err(LocErr::Fs(e)),
            Ok(false) => Ok(None),
            Ok(true) => match fs.real_path(&p) {
                Err(e) => Err(LocErr::Fs(e)),
                Ok(rp) => Ok(Some(rp)),
            },
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:98-103 locateHits
/// `h.2.any (·.isSome)`.
pub fn hit_holds_any(h: &Hit) -> bool {
    let mut i = 0usize;
    while i < h.files.len() {
        if file_some(&h.files[i]) {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:98-103 locateHits
/// `Option.isSome`.
pub fn file_some(o: &Option<Vec<u32>>) -> bool {
    match o {
        Some(_) => true,
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:98-103 locateHits
/// **The search path's directories holding any of module `m`'s files**, in order.
pub fn locate_hits<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, sp: &Vec<Vec<u32>>, m: &NIdx) -> Result<Vec<Hit>, LocErr> {
    let mut out: Vec<Hit> = Vec::new();
    let mut i = 0usize;
    while i < sp.len() {
        match locate_in(fs, pers, ar, m, &sp[i]) {
            Err(e) => return Err(e),
            Ok(h) => out = hits_add(out, h),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:98-103 locateHits
/// `hs.filter fun h => h.2.any (·.isSome)`, one element.
pub fn hits_add(out: Vec<Hit>, h: Hit) -> Vec<Hit> {
    let mut out = out;
    if hit_holds_any(&h) {
        out.push(h);
    }
    out
}

/// con-leche: none — `List (Option String)`'s `==`
pub fn file_lists_eq(a: &Vec<Option<Vec<u32>>>, b: &Vec<Option<Vec<u32>>>) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut i = 0usize;
    while i < a.len() {
        if !file_opt_eq(&a[i], &b[i]) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: none — `Option String`'s `==`
pub fn file_opt_eq(a: &Option<Vec<u32>>, b: &Option<Vec<u32>>) -> bool {
    match (a, b) {
        (None, None) => true,
        (Some(x), Some(y)) => name::str_eq(x, y),
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// `acc.any (·.2 == h.2)`.
pub fn hit_seen(hits: &Vec<Hit>, locs: &Vec<usize>, h: &Hit) -> bool {
    let mut i = 0usize;
    while i < locs.len() {
        if file_lists_eq(&hits[locs[i]].files, &h.files) {
            return true;
        }
        i += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// The locations: the directories up to real paths, first spelling kept, as
/// positions in `hits`.
pub fn hit_locations(hits: &Vec<Hit>) -> Vec<usize> {
    let mut locs: Vec<usize> = Vec::new();
    let mut i = 0usize;
    while i < hits.len() {
        if !hit_seen(hits, &locs, &hits[i]) {
            locs.push(i);
        }
        i += 1;
    }
    locs
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// `rs.any (· != r)`, for location `a`'s file `f` against the locations'.
pub fn file_differs_from(hits: &Vec<Hit>, locs: &Vec<usize>, f: usize, x: &Vec<u32>) -> bool {
    let mut b = 0usize;
    while b < locs.len() {
        if file_other(&hits[locs[b]].files[f], x) {
            return true;
        }
        b += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// A present file that is not `x`.
pub fn file_other(o: &Option<Vec<u32>>, x: &Vec<u32>) -> bool {
    match o {
        Some(y) => !name::str_eq(x, y),
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// `rs.any fun r => rs.any (· != r)`: file `f` has two real paths.
pub fn file_twice_at(hits: &Vec<Hit>, locs: &Vec<usize>, f: usize) -> bool {
    let mut a = 0usize;
    while a < locs.len() {
        if file_at_differs(hits, locs, f, a) {
            return true;
        }
        a += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// Location `a`'s file `f`, against the other locations'.
pub fn file_at_differs(hits: &Vec<Hit>, locs: &Vec<usize>, f: usize, a: usize) -> bool {
    match &hits[locs[a]].files[f] {
        Some(x) => file_differs_from(hits, locs, f, x),
        None => false,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// `(List.range 3).any …`: one of the files with two real paths.
pub fn file_twice(hits: &Vec<Hit>, locs: &Vec<usize>) -> bool {
    let mut f = 0usize;
    while f < 3 {
        if file_twice_at(hits, locs, f) {
            return true;
        }
        f += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// `", ".intercalate (xs.toList.map (·.1.toString))`.
pub fn locs_dirs(hits: &Vec<Hit>, locs: &Vec<usize>) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0usize;
    while i < locs.len() {
        if i > 0 {
            out = text::cat(out, &{ const M: [u32; 2] = [44, 32]; crate::kernel::core_types::code_points(&M) });
        }
        out = text::cat(out, &region::display_path(&hits[locs[i]].dir));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// `desc`: what one location holds.
pub fn loc_desc(mt: &Vec<u32>, h: &Hit) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut first = true;
    let mut i = 0usize;
    while i < h.files.len() {
        if file_some(&h.files[i]) {
            if !first {
                out = text::cat(out, &{ const M: [u32; 2] = [44, 32]; crate::kernel::core_types::code_points(&M) });
            }
            first = false;
            out = text::cat(out, mt);
            out = text::cat(out, &{ const M: [u32; 1] = [46]; crate::kernel::core_types::code_points(&M) });
            out = text::cat(out, &part_ext(i));
        }
        i += 1;
    }
    out = text::cat(out, &{ const M: [u32; 4] = [32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
    text::cat(out, &region::display_path(&h.dir))
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// `"; ".intercalate (locs.toList.map desc)`.
pub fn locs_desc(mt: &Vec<u32>, hits: &Vec<Hit>, locs: &Vec<usize>) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0usize;
    while i < locs.len() {
        if i > 0 {
            out = text::cat(out, &{ const M: [u32; 2] = [59, 32]; crate::kernel::core_types::code_points(&M) });
        }
        out = text::cat(out, &loc_desc(mt, &hits[locs[i]]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// **The module's location from the directories holding its files**, or why there
/// is none.
pub fn locate_of(mt: &Vec<u32>, hits: &Vec<Hit>) -> Result<Located, CheckError> {
    let pre = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, mt);
    if hits.len() == 0 {
        return Err(core_types::internal(text::cat(pre, &{ const M: [u32; 30] = [58, 32, 110, 111, 32, 46, 111, 108, 101, 97, 110, 32, 111, 110, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 32, 112, 97, 116, 104]; crate::kernel::core_types::code_points(&M) })));
    }
    let locs = hit_locations(hits);
    if locs.len() > 1 {
        if file_twice(hits, &locs) {
            let t = text::cat(pre, &{ const M: [u32; 62] = [58, 32, 105, 116, 115, 32, 102, 105, 108, 101, 115, 32, 97, 114, 101, 32, 105, 110, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 111, 110, 101, 32, 108, 111, 99, 97, 116, 105, 111, 110, 32, 111, 110, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 32, 112, 97, 116, 104, 32, 40]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, &locs_dirs(hits, &locs));
            return Err(core_types::internal(text::cat(t, &{ const M: [u32; 45] = [41, 59, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 32, 112, 97, 116, 104, 32, 109, 117, 115, 116, 32, 104, 111, 108, 100, 32, 101, 97, 99, 104, 32, 109, 111, 100, 117, 108, 101, 32, 111, 110, 99, 101]; crate::kernel::core_types::code_points(&M) })));
        }
        let t = text::cat(pre, &{ const M: [u32; 42] = [58, 32, 105, 116, 115, 32, 112, 97, 114, 116, 115, 32, 97, 114, 101, 32, 115, 112, 108, 105, 116, 32, 97, 99, 114, 111, 115, 115, 32, 100, 105, 114, 101, 99, 116, 111, 114, 105, 101, 115, 32, 40]; crate::kernel::core_types::code_points(&M) });
        let t = text::cat(t, &locs_desc(mt, hits, &locs));
        return Err(core_types::internal(text::cat(t, &{ const M: [u32; 44] = [41, 59, 32, 97, 32, 109, 111, 100, 117, 108, 101, 39, 115, 32, 102, 105, 108, 101, 115, 32, 109, 117, 115, 116, 32, 98, 101, 32, 105, 110, 32, 111, 110, 101, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121]; crate::kernel::core_types::code_points(&M) })));
    }
    located_at(mt, pre, &hits[0])
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// `" and ".intercalate held`: the parts held without their `.olean`.
pub fn parts_held(mt: &Vec<u32>, has_s: bool, has_p: bool) -> Vec<u32> {
    if has_s && has_p {
        let t = text::cat(expr::str_copy(mt), &{ const M: [u32; 18] = [46, 111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114, 32, 97, 110, 100, 32]; crate::kernel::core_types::code_points(&M) });
        let t = text::cat(t, mt);
        text::cat(t, &{ const M: [u32; 14] = [46, 111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) })
    } else if has_s {
        text::cat(expr::str_copy(mt), &{ const M: [u32; 13] = [46, 111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) })
    } else {
        text::cat(expr::str_copy(mt), &{ const M: [u32; 14] = [46, 111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) })
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:105-137 locateOf
/// The one location's verdict: it holds the `.olean`, or the parts stand alone.
pub fn located_at(mt: &Vec<u32>, pre: Vec<u32>, h0: &Hit) -> Result<Located, CheckError> {
    let has_o = file_some(&h0.files[0]);
    let has_s = file_some(&h0.files[1]);
    let has_p = file_some(&h0.files[2]);
    if has_o {
        Ok(Located { dir: expr::str_copy(&h0.dir), has_server: has_s, has_private: has_p })
    } else {
        let t = text::cat(pre, &{ const M: [u32; 2] = [58, 32]; crate::kernel::core_types::code_points(&M) });
        let t = text::cat(t, &parts_held(mt, has_s, has_p));
        let t = text::cat(t, &{ const M: [u32; 9] = [32, 119, 105, 116, 104, 111, 117, 116, 32]; crate::kernel::core_types::code_points(&M) });
        let t = text::cat(t, mt);
        let t = text::cat(t, &{ const M: [u32; 10] = [46, 111, 108, 101, 97, 110, 32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
        Err(core_types::internal(text::cat(t, &region::display_path(&h0.dir))))
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:24-26 SearchPath
/// con-leche: ConLeche/Frontend/Olean/Files.lean:139-160 findModule
/// **Find a module, strictly.**
pub fn find_module<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, sp: &Vec<Vec<u32>>, m: &NIdx) -> Result<Located, CheckError> {
    let mt = view::name_text(pers, ar, m);
    match locate_hits(fs, pers, ar, sp, m) {
        Ok(hits) => locate_of(&mt, &hits),
        Err(LocErr::Err(e)) => Err(e),
        Err(LocErr::Fs(e)) => {
            let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &mt);
            let t = text::cat(t, &{ const M: [u32; 22] = [58, 32, 108, 111, 99, 97, 116, 105, 110, 103, 32, 105, 116, 115, 32, 102, 105, 108, 101, 115, 58, 32]; crate::kernel::core_types::code_points(&M) });
            Err(core_types::internal(text::cat(t, &e)))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:162-166 readPart
/// Read and validate one file.
pub fn read_part<F: OleanFs>(fs: &F, p: &Vec<u32>) -> Result<Part, CheckError> {
    match fs.read_bin_file(p) {
        Err(e) => Err(core_types::internal(e)),
        Ok(b) => region::part_of_bytes(p, b),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:168-170 hdrChunk
/// The header read's chunk size.
pub const HDR_CHUNK: u64 = 4096;

/// con-leche: ConLeche/Frontend/Olean/Files.lean:181-183 hdrFin
/// con-leche: ConLeche/Frontend/Olean/Files.lean:172-179 hdrStep
/// The header validated and the imports decoded from the bytes read.
pub fn hdr_fin(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, path: &Vec<u32>, acc: Vec<u8>) -> Result<Vec<ImportRec>, RdErr> {
    match region::part_of_bytes(path, acc) {
        Err(e) => Err(RdErr::Err(e)),
        Ok(p) => header::imports_pre(pk, pers, ar, &p.bytes),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:172-179 hdrStep
/// `hdrWalk acc dataStart` ran off the bytes read.
pub fn hdr_short(acc: &Vec<u8>) -> bool {
    match header::hdr_walk(acc, region::DATA_START) {
        HdrWalk::Short => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:171-186 foldReads
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::read_hdr_bytes_refines, then delete this line
/// The reads of the header: forward in `HDR_CHUNK` reads until the walk to the
/// imports array is inside what was read, or the end of the file.
pub fn read_hdr_bytes<F: OleanFs>(fs: &F, p: &Vec<u32>, size: u64) -> Result<Vec<u8>, CheckError> {
    let mut acc: Vec<u8> = Vec::new();
    let mut off = 0u64;
    let mut more = true;
    while more && off < size {
        match fs.read_range(p, off, HDR_CHUNK) {
            Err(e) => return Err(core_types::internal(e)),
            Ok(c) => acc.extend_from_slice(&c),
        }
        off += if HDR_CHUNK < size - off { HDR_CHUNK } else { size - off };
        more = hdr_short(&acc);
    }
    Ok(acc)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:185-197 readImportsAt
/// con-leche: ConLeche/Frontend/CheckerIO.lean:188-198 foldChunks
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::read_imports_at_refines, then delete this line
/// con-leche: ConLeche/Frontend/CheckerIO.lean:171-186 foldReads
/// con-leche: CHANGED since 701d72ae — re-port, re-test, re-prove files::read_imports_at_refines, then delete this line
/// **A module's imports, read off the start of its exported `.olean`** at its
/// location: the file read forward in `HDR_CHUNK` reads until the walk to the
/// imports array is inside what was read.
pub fn read_imports_at<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, loc: &Located, m: &NIdx) -> Result<Vec<ImportRec>, CheckError> {
    let p = match mod_file(pers, ar, &loc.dir, m, &{ const M: [u32; 5] = [111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let size = match fs.file_size(&p) {
        Err(e) => return Err(core_types::internal(e)),
        Ok(s) => s,
    };
    let acc: Vec<u8> = match read_hdr_bytes(fs, &p, size) {
        Err(e) => return Err(e),
        Ok(acc) => acc,
    };
    match hdr_fin(pk, pers, ar, &p, acc) {
        Ok(imps) => Ok(imps),
        Err(RdErr::Err(e)) => Err(e),
        Err(RdErr::Bad) => Err(view::undecodable(pers, ar, m)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:199-205 moduleImports
/// **A module's imports**, off the start of its exported `.olean`, located on the
/// search path.
pub fn module_imports<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, m: &NIdx) -> Result<Vec<ImportRec>, CheckError> {
    match find_module(fs, pers, ar, sp, m) {
        Err(e) => Err(e),
        Ok(loc) => read_imports_at(fs, pk, pers, ar, &loc, m),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:207-236 readFiles
/// `module {m}: a module of the module system without its {m}.{ext} in {dir}`.
pub fn missing_part(pers: &PersTier, ar: &EStore, m: &NIdx, mt: &Vec<u32>, ext: &Vec<u32>, dir: &Vec<u32>) -> CheckError {
    let t = text::cat({ const M: [u32; 42] = [97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 102, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 32, 119, 105, 116, 104, 111, 117, 116, 32, 105, 116, 115, 32]; crate::kernel::core_types::code_points(&M) }, mt);
    let t = text::cat(t, ext);
    let t = text::cat(t, &{ const M: [u32; 4] = [32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
    module::bad_module(pers, ar, m, text::cat(t, &region::display_path(dir)))
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:207-236 readFiles
/// **The files of a module a view reads**, each validated, located on the search
/// path.  A part beside a classic `.olean` is no part of it, and a module of the
/// module system has all three.
pub fn read_files<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, sp: &Vec<Vec<u32>>, m: &NIdx, level: &OLeanLevel) -> Result<ModFiles, CheckError> {
    let loc = match find_module(fs, pers, ar, sp, m) {
        Err(e) => return Err(e),
        Ok(l) => l,
    };
    let mt = view::name_text(pers, ar, m);
    let p_o = match mod_file(pers, ar, &loc.dir, m, &{ const M: [u32; 5] = [111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let ex = match read_part(fs, &p_o) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    match level {
        OLeanLevel::Exported => return Ok(ModFiles { exported: ex, server: None, private_part: None }),
        _ => {}
    }
    let f = ModFiles { exported: ex, server: None, private_part: None };
    if !view::mod_files_is_module(&f) {
        if loc.has_server || loc.has_private {
            let t = text::cat({ const M: [u32; 40] = [97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 117, 116, 115, 105, 100, 101, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 32, 40, 105, 116, 115, 32]; crate::kernel::core_types::code_points(&M) }, &mt);
            let t = text::cat(t, &{ const M: [u32; 14] = [46, 111, 108, 101, 97, 110, 41, 44, 32, 119, 105, 116, 104, 32]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, &mt);
            let t = if loc.has_private {
                text::cat(t, &{ const M: [u32; 14] = [46, 111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) })
            } else {
                text::cat(t, &{ const M: [u32; 13] = [46, 111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) })
            };
            let t = text::cat(t, &{ const M: [u32; 14] = [32, 98, 101, 115, 105, 100, 101, 32, 105, 116, 32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
            return Err(module::bad_module(pers, ar, m, text::cat(t, &region::display_path(&loc.dir))));
        }
        return Ok(f);
    }
    if !loc.has_server {
        return Err(missing_part(pers, ar, m, &mt, &{ const M: [u32; 13] = [46, 111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }, &loc.dir));
    }
    if !loc.has_private {
        return Err(missing_part(pers, ar, m, &mt, &{ const M: [u32; 14] = [46, 111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }, &loc.dir));
    }
    read_files_parts(fs, pers, ar, m, &loc, f, level)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:207-236 readFiles
/// The rest of `readFiles`: the server part, and the private part unless the
/// level stops short of it.
pub fn read_files_parts<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, m: &NIdx, loc: &Located, f: ModFiles, level: &OLeanLevel) -> Result<ModFiles, CheckError> {
    let p_s = match mod_file(pers, ar, &loc.dir, m, &{ const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let s = match read_part(fs, &p_s) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    match level {
        OLeanLevel::Server => return Ok(ModFiles { exported: f.exported, server: Some(s), private_part: None }),
        _ => {}
    }
    let p_p = match mod_file(pers, ar, &loc.dir, m, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    match read_part(fs, &p_p) {
        Err(e) => Err(e),
        Ok(p) => Ok(ModFiles { exported: f.exported, server: Some(s), private_part: Some(p) }),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:238-246 readView
/// **One view of a module**, located on the search path.
pub fn read_view<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, m: &NIdx, level: &OLeanLevel) -> Result<ModDecoded, CheckError> {
    match read_files(fs, pers, ar, sp, m, level) {
        Err(e) => Err(e),
        Ok(f) => match view::parse_view(pk, pers, ar, &f, level) {
            Ok(d) => Ok(d),
            Err(RdErr::Err(e)) => Err(e),
            Err(RdErr::Bad) => Err(view::view_error(pk, pers, ar, m, &f, level)),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:248-261 readAllViews
/// `([.exported, .server].find? fun l => (parseView f l).isNone).getD .private`.
pub fn first_bad_view(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, f: &ModFiles) -> Result<OLeanLevel, CheckError> {
    match view::parse_view(pk, pers, ar, f, &OLeanLevel::Exported) {
        Err(RdErr::Err(e)) => return Err(e),
        Err(RdErr::Bad) => return Ok(OLeanLevel::Exported),
        Ok(_) => {}
    }
    match view::parse_view(pk, pers, ar, f, &OLeanLevel::Server) {
        Err(RdErr::Err(e)) => Err(e),
        Err(RdErr::Bad) => Ok(OLeanLevel::Server),
        Ok(_) => Ok(OLeanLevel::Private),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:248-261 readAllViews
/// **All three views of a module, checked against each other**: its home's read.
pub fn read_all_views<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Vec<Vec<u32>>, m: &NIdx) -> Result<(AllViews, Vec<Expo>), CheckError> {
    let f = match read_files(fs, pers, ar, sp, m, &OLeanLevel::Private) {
        Err(e) => return Err(e),
        Ok(f) => f,
    };
    match view::parse_all_views(pk, pers, ar, &f) {
        Err(RdErr::Err(e)) => Err(e),
        Err(RdErr::Bad) => match first_bad_view(pk, pers, ar, &f) {
            Err(e) => Err(e),
            Ok(level) => Err(view::view_error(pk, pers, ar, m, &f, &level)),
        },
        Ok(v) => match module::check_views(pk, pers, ar, m, &f, &v) {
            Err(e) => Err(e),
            Ok(expo) => Ok((v, expo)),
        },
    }
}

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
use crate::frontend::olean::reads::NamePositions;
use crate::frontend::olean::region;
use crate::frontend::olean::region::Part;
use crate::frontend::olean::spec;
use crate::frontend::olean::spec::{ImportRec, ModDecoded, OleanPins, RdErr};
use crate::frontend::olean::view;
use crate::frontend::olean::view::{AllViews, ModFiles, OLeanLevel};
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::expr;
use crate::kernel::name;
use crate::kernel::name::Name;
use crate::kernel::name::NameKind;

/// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
/// **The checker's file reads**: the operations of upstream's class the reader
/// uses, and the read's heartbeat, two of the `liftIO` actions upstream hands
/// the class.  A failure is the operation's message.  The class's worker map
/// (`parMapWorkers`) is the check pool's, in `crates/con-ron`.
pub trait OleanFs {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// whether the path names something (a file, a directory)
    fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// whether the path names a directory (through symbolic links)
    fn is_dir(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// the path with every symbolic link resolved, absolute
    fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// a regular file's bytes
    fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// a positional read: the bytes from `off` up to `off + len` or the end of
    /// the file, whichever comes first.  Deviation: the class opens a handle
    /// (`openRead`) and reads it forward (`read`), since Lean's handles have no
    /// positional read; Rust's do (`FileExt::read_at`), so this read keeps no
    /// state, and the reads `foldReads` makes, at `0, csz, 2·csz, …`, are the
    /// handle's in order.
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>>;
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
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

/// con-leche: ConLeche/Frontend/Olean/Files.lean:28-35 modDir
/// con-leche: ConLeche/Frontend/Olean/Files.lean:28-35 modDir.comps
/// A module's path below a directory, without an extension: its components as
/// directories.
pub fn mod_dir_of(dir: &Vec<u32>, n: &Name) -> Vec<u32> {
    let cs = name::component_list(n, Vec::new());
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
    path
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:45-47 modFile
/// The file a module's level is stored in, for a name.
pub fn mod_file_of(dir: &Vec<u32>, n: &Name, ext: &Vec<u32>) -> Vec<u32> {
    path_add_extension(&mod_dir_of(dir, n), ext)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:45-47 modFile
/// The file a module's level is stored in, the module a handle.
pub fn mod_file(pers: &PersTier, ar: &EStore, dir: &Vec<u32>, m: &NIdx, ext: &Vec<u32>) -> Result<Vec<u32>, CheckError> {
    match env::read_name(pers, ar, m) {
        Err(e) => Err(e),
        Ok(n) => Ok(mod_file_of(dir, &n, ext)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:37-43 Name.root
/// **A module name's root**: its first component.
pub fn name_root(n: &Name) -> Name {
    match &n.0.kind {
        NameKind::Anonymous => name::anonymous(),
        NameKind::Str(p, s) => match &p.0.kind {
            NameKind::Anonymous => name::mk_str(name::anonymous(), expr::str_copy(s)),
            _ => name_root(p),
        },
        NameKind::Num(p, k) => match &p.0.kind {
            NameKind::Anonymous => name::mk_num(name::anonymous(), *k),
            _ => name_root(p),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:49-51 NameScan
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

/// con-leche: ConLeche/Frontend/Olean/Files.lean:53-56 Name.pushPlain
/// A component as written without an escape: at `nums`, one of digits alone is a
/// number, as Lean's name literals read it.
pub fn name_push_plain(n: Name, cur: Vec<u32>, nums: bool) -> Name {
    if nums && cur.len() > 0 && all_digits(&cur) {
        name::mk_num(n, digits_value(&cur))
    } else {
        name::mk_str(n, cur)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:58-75 scanName
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

/// con-leche: ConLeche/Frontend/Olean/Files.lean:58-75 scanName
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

/// con-leche: ConLeche/Frontend/Olean/Files.lean:77-83 parseModName
/// **A module name as the command line spells it**.
pub fn parse_mod_name(s: &Vec<u32>) -> Option<Name> {
    scan_name(false, s)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:85-88 parseConstName
/// **A constant's name as the command line spells it**.
pub fn parse_const_name(s: &Vec<u32>) -> Option<Name> {
    scan_name(true, s)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:90-100 RootAt
/// **Where a root's modules are**: the one search-path directory holding the root,
/// or why there is none.
pub enum RootAt {
    /// the directory holding it
    Dir(Vec<u32>),
    /// no directory holds it
    Missing,
    /// directories in two or more locations hold it, these (the first spelling of each)
    Twice(Vec<Vec<u32>>),
    /// a failed operation while looking, its message
    Failed(Vec<u32>),
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:116-120 holdsRoot
/// **Whether a directory holds a root**, as Lean asks it: a directory of the
/// root's name, or a file of that name with `.olean`.
pub fn holds_root<F: OleanFs>(fs: &F, r: &Name, d: &Vec<u32>) -> Result<bool, Vec<u32>> {
    match fs.is_dir(&mod_dir_of(d, r)) {
        Err(e) => Err(e),
        Ok(true) => Ok(true),
        Ok(false) => fs.path_exists(&mod_file_of(d, r, &{ const M: [u32; 5] = [111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) })),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:127-138 rootHits
/// The directories holding the root, in search-path order (`held`, filtered).
pub fn root_dirs<F: OleanFs>(fs: &F, sp: &Vec<Vec<u32>>, r: &Name) -> Result<Vec<Vec<u32>>, Vec<u32>> {
    let mut out: Vec<Vec<u32>> = Vec::new();
    let mut i = 0usize;
    while i < sp.len() {
        match holds_root(fs, r, &sp[i]) {
            Err(e) => return Err(e),
            Ok(true) => out.push(expr::str_copy(&sp[i])),
            Ok(false) => {}
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:127-138 rootHits
/// The real path of each directory holding the root, in order.
pub fn real_paths<F: OleanFs>(fs: &F, hits: &Vec<Vec<u32>>) -> Result<Vec<Vec<u32>>, Vec<u32>> {
    let mut out: Vec<Vec<u32>> = Vec::with_capacity(hits.len());
    let mut i = 0usize;
    while i < hits.len() {
        match fs.real_path(&hits[i]) {
            Err(e) => return Err(e),
            Ok(rp) => out.push(rp),
        }
        i += 1;
    }
    Ok(out)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:122-125 oneEach
/// Every real path is the first's: `oneEach` keeps one directory.
pub fn all_same(reals: &Vec<Vec<u32>>) -> bool {
    let mut i = 1usize;
    while i < reals.len() {
        if !name::str_eq(&reals[i], &reals[0]) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:122-125 oneEach
/// The directories, one for each location: real paths compared, the first
/// spelling kept.
pub fn one_each(hits: &Vec<Vec<u32>>, reals: &Vec<Vec<u32>>) -> Vec<Vec<u32>> {
    let mut out: Vec<Vec<u32>> = Vec::new();
    let mut i = 0usize;
    while i < hits.len() {
        if !real_seen(reals, i) {
            out.push(expr::str_copy(&hits[i]));
        }
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:122-125 oneEach
/// `acc.any (·.2 == d.2)`: an earlier directory has the real path of the `i`th.
pub fn real_seen(reals: &Vec<Vec<u32>>, i: usize) -> bool {
    let mut j = 0usize;
    while j < i {
        if name::str_eq(&reals[j], &reals[i]) {
            return true;
        }
        j += 1;
    }
    false
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:127-138 rootHits
/// **Where a root's modules are on the search path**: the directories holding
/// the root; where two or more do, their real paths compared, so that a
/// directory listed twice, or reached through a symbolic link, is one location.
pub fn root_hits<F: OleanFs>(fs: &F, sp: &Vec<Vec<u32>>, r: &Name) -> Result<RootAt, Vec<u32>> {
    let hits = match root_dirs(fs, sp, r) {
        Err(e) => return Err(e),
        Ok(h) => h,
    };
    if hits.len() == 0 {
        return Ok(RootAt::Missing);
    }
    if hits.len() == 1 {
        return Ok(RootAt::Dir(expr::str_copy(&hits[0])));
    }
    match real_paths(fs, &hits) {
        Err(e) => Err(e),
        Ok(reals) => {
            if all_same(&reals) {
                Ok(RootAt::Dir(expr::str_copy(&hits[0])))
            } else {
                Ok(RootAt::Twice(one_each(&hits, &reals)))
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:140-142 rootAt
/// `root_hits`, a failed operation its answer's reason.
pub fn root_at<F: OleanFs>(fs: &F, sp: &Vec<Vec<u32>>, r: &Name) -> RootAt {
    match root_hits(fs, sp, r) {
        Ok(a) => a,
        Err(e) => RootAt::Failed(e),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:102-111 Roots
/// **A search path and its fallback**: the directories, and the directories a
/// root none of them holds is looked up on.  Only a compared solution has
/// fallback directories (`--trusted-search-path`: the trusted path first, the
/// search path after it); every other read has none.  Upstream's map of the
/// roots resolved so far is not kept (`find_module`'s note).
pub struct Roots {
    pub path: Vec<Vec<u32>>,
    pub fallback: Vec<Vec<u32>>,
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:113-114 _
/// A search path with no fallback.
pub fn roots_of_path(path: Vec<Vec<u32>>) -> Roots {
    Roots { path, fallback: Vec::new() }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:144-148 lookNext
/// The fallback's turn: where the path holds no directory of the root, the
/// fallback's answer.
pub fn look_next<F: OleanFs>(fs: &F, fallback: &Vec<Vec<u32>>, r: &Name, a: RootAt) -> RootAt {
    match a {
        RootAt::Missing => root_at(fs, fallback, r),
        a => a,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:150-154 lookAt
/// **Where a root's modules are, on a path and its fallback**: on the path, and
/// where no directory of it holds the root, on the fallback.  A root the path
/// holds shadows the fallback's copy; the one-location rule holds on each of the
/// two separately.
pub fn look_at<F: OleanFs>(fs: &F, path: &Vec<Vec<u32>>, fallback: &Vec<Vec<u32>>, r: &Name) -> RootAt {
    look_next(fs, fallback, r, root_at(fs, path, r))
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:167-170 Located
/// **Where a module's files are**: the search-path directory holding its root.
pub struct Located {
    pub dir: Vec<u32>,
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:172-180 locatedOf
/// `", ".intercalate (ds.map toString)`.
pub fn dirs_text(ds: &Vec<Vec<u32>>) -> Vec<u32> {
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0usize;
    while i < ds.len() {
        if i > 0 {
            out = text::cat(out, &{ const M: [u32; 2] = [44, 32]; crate::kernel::core_types::code_points(&M) });
        }
        out = text::cat(out, &region::display_path(&ds[i]));
        i += 1;
    }
    out
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:172-180 locatedOf
/// **The module's location from where its root is**, or why there is none; `mt`
/// and `rt` are the module's and the root's names, as text.
pub fn located_of(mt: &Vec<u32>, rt: &Vec<u32>, a: RootAt) -> Result<Located, CheckError> {
    let pre = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, mt);
    match a {
        RootAt::Dir(d) => Ok(Located { dir: d }),
        RootAt::Missing => {
            let t = text::cat(pre, &{ const M: [u32; 57] = [58, 32, 110, 111, 32, 46, 111, 108, 101, 97, 110, 32, 111, 110, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 32, 112, 97, 116, 104, 32, 40, 110, 111, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 111, 102, 32, 105, 116, 32, 104, 111, 108, 100, 115, 32]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, rt);
            let t = text::cat(t, &{ const M: [u32; 4] = [32, 111, 114, 32]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, rt);
            Err(core_types::internal(text::cat(t, &{ const M: [u32; 7] = [46, 111, 108, 101, 97, 110, 41]; crate::kernel::core_types::code_points(&M) })))
        }
        RootAt::Twice(ds) => {
            let t = text::cat(pre, &{ const M: [u32; 11] = [58, 32, 105, 116, 115, 32, 114, 111, 111, 116, 32]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, rt);
            let t = text::cat(t, &{ const M: [u32; 50] = [32, 105, 115, 32, 105, 110, 32, 109, 111, 114, 101, 32, 116, 104, 97, 110, 32, 111, 110, 101, 32, 108, 111, 99, 97, 116, 105, 111, 110, 32, 111, 110, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 32, 112, 97, 116, 104, 32, 40]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, &dirs_text(&ds));
            Err(core_types::internal(text::cat(t, &{ const M: [u32; 43] = [41, 59, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 32, 112, 97, 116, 104, 32, 109, 117, 115, 116, 32, 104, 111, 108, 100, 32, 101, 97, 99, 104, 32, 114, 111, 111, 116, 32, 111, 110, 99, 101]; crate::kernel::core_types::code_points(&M) })))
        }
        RootAt::Failed(e) => {
            let t = text::cat(pre, &{ const M: [u32; 22] = [58, 32, 108, 111, 99, 97, 116, 105, 110, 103, 32, 105, 116, 115, 32, 102, 105, 108, 101, 115, 58, 32]; crate::kernel::core_types::code_points(&M) });
            Err(core_types::internal(text::cat(t, &e)))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:24-26 SearchPath
/// con-leche: ConLeche/Frontend/Olean/Files.lean:182-202 findModule
/// con-leche: ConLeche/Frontend/Olean/Files.lean:156-160 Roots.rootOf
/// **Find a module, as Lean does, strictly**: the one directory holding its root,
/// on the path or else on the fallback (`look_at`), or why there is none.  Each
/// read looks the root up: upstream's `Roots` map, which resolves each root once
/// per run, is a cache over one snapshot, where the lookup answers the same each
/// time.
pub fn find_module<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, sp: &Roots, m: &NIdx) -> Result<Located, CheckError> {
    match env::read_name(pers, ar, m) {
        Err(e) => Err(e),
        Ok(n) => {
            let r = name_root(&n);
            let a = look_at(fs, &sp.path, &sp.fallback, &r);
            located_of(&name::render(&n), &name::render(&r), a)
        }
    }
}

/// con-leche: none — `a ++ "." ++ ext`, a part's file name
pub fn part_name(mt: &Vec<u32>, ext: &Vec<u32>) -> Vec<u32> {
    let t = text::cat(expr::str_copy(mt), &{ const M: [u32; 1] = [46]; crate::kernel::core_types::code_points(&M) });
    text::cat(t, ext)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:204-218 oleanFailed
/// **Why a module's `.olean` cannot be read at its location**: it is not there,
/// with or without parts beside it, or it is there and cannot be read.  A failed
/// `path_exists` is its message.
pub fn olean_failed<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, loc: &Located, m: &NIdx) -> CheckError {
    let p_o = match mod_file(pers, ar, &loc.dir, m, &{ const M: [u32; 5] = [111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return e,
        Ok(p) => p,
    };
    let mt = view::name_text(pers, ar, m);
    match fs.path_exists(&p_o) {
        Err(e) => return core_types::internal(e),
        Ok(true) => {
            let t = text::cat(region::display_path(&p_o), &{ const M: [u32; 15] = [32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 114, 101, 97, 100]; crate::kernel::core_types::code_points(&M) });
            return module::bad_module(pers, ar, m, t);
        }
        Ok(false) => {}
    }
    let has_s = match path_exists_at(fs, pers, ar, loc, m, &{ const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return e,
        Ok(b) => b,
    };
    let has_p = match path_exists_at(fs, pers, ar, loc, m, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return e,
        Ok(b) => b,
    };
    if !has_s && !has_p {
        let t = text::cat({ const M: [u32; 3] = [110, 111, 32]; crate::kernel::core_types::code_points(&M) }, &mt);
        let t = text::cat(t, &{ const M: [u32; 10] = [46, 111, 108, 101, 97, 110, 32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
        let t = text::cat(t, &region::display_path(&loc.dir));
        let t = text::cat(t, &{ const M: [u32; 45] = [44, 32, 116, 104, 101, 32, 115, 101, 97, 114, 99, 104, 45, 112, 97, 116, 104, 32, 100, 105, 114, 101, 99, 116, 111, 114, 121, 32, 104, 111, 108, 100, 105, 110, 103, 32, 105, 116, 115, 32, 114, 111, 111, 116, 32]; crate::kernel::core_types::code_points(&M) });
        let rt = match env::read_name(pers, ar, m) {
            Ok(n) => name::render(&name_root(&n)),
            Err(_) => { const M: [u32; 1] = [63]; crate::kernel::core_types::code_points(&M) },
        };
        return module::bad_module(pers, ar, m, text::cat(t, &rt));
    }
    let held = if has_s && has_p {
        let t = text::cat(part_name(&mt, &{ const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }), &{ const M: [u32; 5] = [32, 97, 110, 100, 32]; crate::kernel::core_types::code_points(&M) });
        text::cat(t, &part_name(&mt, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }))
    } else if has_s {
        part_name(&mt, &{ const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) })
    } else {
        part_name(&mt, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) })
    };
    let t = text::cat(held, &{ const M: [u32; 9] = [32, 119, 105, 116, 104, 111, 117, 116, 32]; crate::kernel::core_types::code_points(&M) });
    let t = text::cat(t, &mt);
    let t = text::cat(t, &{ const M: [u32; 10] = [46, 111, 108, 101, 97, 110, 32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
    module::bad_module(pers, ar, m, text::cat(t, &region::display_path(&loc.dir)))
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:232-238 partFailed
/// Why a part of a module of the module system cannot be read at its location.
pub fn part_failed<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, loc: &Located, m: &NIdx, ext: &Vec<u32>) -> CheckError {
    let p = match mod_file(pers, ar, &loc.dir, m, ext) {
        Err(e) => return e,
        Ok(p) => p,
    };
    match fs.path_exists(&p) {
        Err(e) => core_types::internal(e),
        Ok(true) => module::bad_module(pers, ar, m, text::cat(region::display_path(&p), &{ const M: [u32; 15] = [32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 114, 101, 97, 100]; crate::kernel::core_types::code_points(&M) })),
        Ok(false) => {
            let mt = view::name_text(pers, ar, m);
            missing_part(pers, ar, m, &mt, &part_name(&{ const M: [u32; 0] = []; crate::kernel::core_types::code_points(&M) }, ext), &loc.dir)
        }
    }
}

/// con-leche: none — `pathExists` of a module's file at its location, a failure its
/// message
pub fn path_exists_at<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, loc: &Located, m: &NIdx, ext: &Vec<u32>) -> Result<bool, CheckError> {
    match mod_file(pers, ar, &loc.dir, m, ext) {
        Err(e) => Err(e),
        Ok(p) => match fs.path_exists(&p) {
            Err(e) => Err(core_types::internal(e)),
            Ok(b) => Ok(b),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:220-224 readPart
/// con-leche: ConLeche/Frontend/Olean/Files.lean:226-230 readPartOr
/// **Read and validate one of a module's files** at its location: `ext`'s, a file
/// that cannot be read `olean_failed`'s error (`olean`) or `part_failed`'s.
pub fn read_part_at<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, loc: &Located, m: &NIdx, ext: &Vec<u32>, olean: bool) -> Result<Part, CheckError> {
    let p = match mod_file(pers, ar, &loc.dir, m, ext) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    match fs.read_bin_file(&p) {
        Err(_) => {
            if olean {
                Err(olean_failed(fs, pers, ar, loc, m))
            } else {
                Err(part_failed(fs, pers, ar, loc, m, ext))
            }
        }
        Ok(b) => region::part_of_bytes(&p, b),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:240-242 hdrChunk
/// The header read's chunk size.
pub const HDR_CHUNK: u64 = 4096;

/// con-leche: ConLeche/Frontend/Olean/Files.lean:253-255 hdrFin
/// con-leche: ConLeche/Frontend/Olean/Files.lean:244-251 hdrStep
/// The header validated and the imports decoded from the bytes read.
pub fn hdr_fin(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, path: &Vec<u32>, acc: Vec<u8>) -> Result<Vec<ImportRec>, RdErr> {
    match region::part_of_bytes(path, acc) {
        Err(e) => Err(RdErr::Err(e)),
        Ok(p) => header::imports_pre(pk, pers, ar, &p.bytes),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:244-251 hdrStep
/// `hdrWalk acc dataStart` ran off the bytes read.
pub fn hdr_short(acc: &Vec<u8>) -> bool {
    match header::hdr_walk(acc, region::DATA_START) {
        HdrWalk::Short => true,
        _ => false,
    }
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:188-203 foldReads
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

/// con-leche: ConLeche/Frontend/Olean/Files.lean:257-271 readImportsAt
/// con-leche: ConLeche/Frontend/CheckerIO.lean:205-215 foldChunks
/// con-leche: ConLeche/Frontend/CheckerIO.lean:188-203 foldReads
/// **A module's imports, read off the start of its exported `.olean`** at its
/// location: the file read forward in `HDR_CHUNK` reads until the walk to the
/// imports array is inside what was read.  A file that cannot be read is
/// `olean_failed`'s error.
pub fn read_imports_at<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, loc: &Located, m: &NIdx) -> Result<Vec<ImportRec>, CheckError> {
    let p = match mod_file(pers, ar, &loc.dir, m, &{ const M: [u32; 5] = [111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) }) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    let size = match fs.file_size(&p) {
        Err(_) => return Err(olean_failed(fs, pers, ar, loc, m)),
        Ok(s) => s,
    };
    let acc: Vec<u8> = match read_hdr_bytes(fs, &p, size) {
        Err(_) => return Err(olean_failed(fs, pers, ar, loc, m)),
        Ok(acc) => acc,
    };
    match hdr_fin(pk, pers, ar, &p, acc) {
        Ok(imps) => Ok(imps),
        Err(RdErr::Err(e)) => Err(e),
        Err(RdErr::Bad) => Err(view::undecodable(pers, ar, m)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:273-279 moduleImports
/// **A module's imports**, off the start of its exported `.olean`, located on the
/// search path.
pub fn module_imports<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Roots, m: &NIdx) -> Result<Vec<ImportRec>, CheckError> {
    match find_module(fs, pers, ar, sp, m) {
        Err(e) => Err(e),
        Ok(loc) => read_imports_at(fs, pk, pers, ar, &loc, m),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:297-325 readFilesAt
/// `module {m}: a module of the module system without its {m}.{ext} in {dir}`.
pub fn missing_part(pers: &PersTier, ar: &EStore, m: &NIdx, mt: &Vec<u32>, ext: &Vec<u32>, dir: &Vec<u32>) -> CheckError {
    let t = text::cat({ const M: [u32; 42] = [97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 102, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 32, 119, 105, 116, 104, 111, 117, 116, 32, 105, 116, 115, 32]; crate::kernel::core_types::code_points(&M) }, mt);
    let t = text::cat(t, ext);
    let t = text::cat(t, &{ const M: [u32; 4] = [32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
    module::bad_module(pers, ar, m, text::cat(t, &region::display_path(dir)))
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:281-295 outsideOrEscaping
/// **An `M.olean` that is not a module of the module system, with a part beside
/// it.**  Where `M.olean` does not read on its own, it is a malformed exported
/// part (`.invalid`, exit 1): an exported part must not point into its
/// `.olean.server` or `.olean.private`.  Otherwise it is a module outside the
/// module system with a stray part beside it.
pub fn outside_or_escaping(pers: &PersTier, ar: &EStore, loc: &Located, m: &NIdx, ex: &Part, has_private: bool) -> CheckError {
    let mt = view::name_text(pers, ar, m);
    let r = region::region_single(ex);
    match spec::module_skel(&ex.bytes, &r, region::part_module_data_addr(ex)) {
        None => {
            let t = text::cat({ const M: [u32; 7] = [109, 111, 100, 117, 108, 101, 32]; crate::kernel::core_types::code_points(&M) }, &mt);
            let t = text::cat(t, &{ const M: [u32; 20] = [58, 32, 105, 116, 115, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 112, 97, 114, 116, 32]; crate::kernel::core_types::code_points(&M) });
            let t = text::cat(t, &mt);
            let t = text::cat(t, &{ const M: [u32; 129] = [46, 111, 108, 101, 97, 110, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 114, 101, 97, 100, 32, 111, 110, 32, 105, 116, 115, 32, 111, 119, 110, 32, 40, 97, 110, 32, 101, 120, 112, 111, 114, 116, 101, 100, 32, 112, 97, 114, 116, 32, 109, 117, 115, 116, 32, 110, 111, 116, 32, 112, 111, 105, 110, 116, 32, 111, 117, 116, 115, 105, 100, 101, 32, 105, 116, 115, 32, 102, 105, 108, 101, 44, 32, 105, 110, 116, 111, 32, 105, 116, 115, 32, 46, 111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114, 32, 111, 114, 32, 46, 111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101, 41, 44, 32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
            core_types::invalid(text::cat(t, &region::display_path(&loc.dir)))
        }
        Some(_) => {
            let t = text::cat({ const M: [u32; 40] = [97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 117, 116, 115, 105, 100, 101, 32, 116, 104, 101, 32, 109, 111, 100, 117, 108, 101, 32, 115, 121, 115, 116, 101, 109, 32, 40, 105, 116, 115, 32]; crate::kernel::core_types::code_points(&M) }, &mt);
            let t = text::cat(t, &{ const M: [u32; 14] = [46, 111, 108, 101, 97, 110, 41, 44, 32, 119, 105, 116, 104, 32]; crate::kernel::core_types::code_points(&M) });
            let t = if has_private {
                text::cat(t, &part_name(&mt, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }))
            } else {
                text::cat(t, &part_name(&mt, &{ const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }))
            };
            let t = text::cat(t, &{ const M: [u32; 14] = [32, 98, 101, 115, 105, 100, 101, 32, 105, 116, 32, 105, 110, 32]; crate::kernel::core_types::code_points(&M) });
            module::bad_module(pers, ar, m, text::cat(t, &region::display_path(&loc.dir)))
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:297-325 readFilesAt
/// **The files of a module a view reads at its location**, each validated.  A
/// part beside a classic `.olean` is no part of it, and a module of the module
/// system has all three: reading the parts a view needs says whether they are
/// there, and a server view asks for the private part's existence besides.
pub fn read_files_at<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, loc: &Located, m: &NIdx, level: &OLeanLevel) -> Result<ModFiles, CheckError> {
    let ex = match read_part_at(fs, pers, ar, loc, m, &{ const M: [u32; 5] = [111, 108, 101, 97, 110]; crate::kernel::core_types::code_points(&M) }, true) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    match level {
        OLeanLevel::Exported => return Ok(ModFiles { exported: ex, server: None, private_part: None }),
        _ => {}
    }
    let f = ModFiles { exported: ex, server: None, private_part: None };
    if !view::mod_files_is_module(&f) {
        let has_s = match path_exists_at(fs, pers, ar, loc, m, &{ const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }) {
            Err(e) => return Err(e),
            Ok(b) => b,
        };
        let has_p = match path_exists_at(fs, pers, ar, loc, m, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }) {
            Err(e) => return Err(e),
            Ok(b) => b,
        };
        if has_s || has_p {
            return Err(outside_or_escaping(pers, ar, loc, m, &f.exported, has_p));
        }
        return Ok(f);
    }
    read_files_parts(fs, pers, ar, m, loc, f, level)
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:297-325 readFilesAt
/// The rest of `readFilesAt`: the server part, then the private part's existence
/// at the server level, or the private part.
pub fn read_files_parts<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, m: &NIdx, loc: &Located, f: ModFiles, level: &OLeanLevel) -> Result<ModFiles, CheckError> {
    let s = match read_part_at(fs, pers, ar, loc, m, &{ const M: [u32; 12] = [111, 108, 101, 97, 110, 46, 115, 101, 114, 118, 101, 114]; crate::kernel::core_types::code_points(&M) }, false) {
        Err(e) => return Err(e),
        Ok(p) => p,
    };
    match level {
        OLeanLevel::Server => {
            return match path_exists_at(fs, pers, ar, loc, m, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }) {
                Err(e) => Err(e),
                Ok(true) => Ok(ModFiles { exported: f.exported, server: Some(s), private_part: None }),
                Ok(false) => {
                    let mt = view::name_text(pers, ar, m);
                    Err(missing_part(pers, ar, m, &mt, &{ const M: [u32; 14] = [46, 111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }, &loc.dir))
                }
            };
        }
        _ => {}
    }
    match read_part_at(fs, pers, ar, loc, m, &{ const M: [u32; 13] = [111, 108, 101, 97, 110, 46, 112, 114, 105, 118, 97, 116, 101]; crate::kernel::core_types::code_points(&M) }, false) {
        Err(e) => Err(e),
        Ok(p) => Ok(ModFiles { exported: f.exported, server: Some(s), private_part: Some(p) }),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:327-333 readFiles
/// **The files of a module a view reads**, located on the search path
/// (`find_module`), then read at that location (`read_files_at`).
pub fn read_files<F: OleanFs>(fs: &F, pers: &PersTier, ar: &EStore, sp: &Roots, m: &NIdx, level: &OLeanLevel) -> Result<ModFiles, CheckError> {
    match find_module(fs, pers, ar, sp, m) {
        Err(e) => Err(e),
        Ok(loc) => read_files_at(fs, pers, ar, &loc, m, level),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:335-343 readView
/// **One view of a module**, located on the search path.
pub fn read_view<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Roots, m: &NIdx, level: &OLeanLevel) -> Result<ModDecoded, CheckError> {
    match read_files(fs, pers, ar, sp, m, level) {
        Err(e) => Err(e),
        Ok(f) => match view::parse_view(pk, pers, ar, &f, level) {
            Ok(d) => Ok(d),
            Err(RdErr::Err(e)) => Err(e),
            Err(RdErr::Bad) => Err(view::view_error(pk, pers, ar, m, &f, level)),
        },
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:345-350 namesOf
/// **A part's name positions, off its files** (`read_name_positions`, with the
/// reason where they do not read).
pub fn names_of(pk: &OleanPins, pers: &PersTier, ar: &mut EStore, m: &NIdx, f: &ModFiles, level: &OLeanLevel) -> Result<NamePositions, CheckError> {
    match view::read_name_positions(pk, pers, ar, f, level) {
        Ok(ps) => Ok(ps),
        Err(RdErr::Err(e)) => Err(e),
        Err(RdErr::Bad) => Err(view::view_error(pk, pers, ar, m, f, level)),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:352-357 readPartNamesAt
/// **One part's name positions**, read off its files at their location.
pub fn read_part_names_at<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, loc: &Located, m: &NIdx, level: &OLeanLevel) -> Result<NamePositions, CheckError> {
    match read_files_at(fs, pers, ar, loc, m, level) {
        Err(e) => Err(e),
        Ok(f) => names_of(pk, pers, ar, m, &f, level),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:359-364 readPartNames
/// **One part's name positions**, located on the search path.
pub fn read_part_names<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Roots, m: &NIdx, level: &OLeanLevel) -> Result<NamePositions, CheckError> {
    match find_module(fs, pers, ar, sp, m) {
        Err(e) => Err(e),
        Ok(loc) => read_part_names_at(fs, pk, pers, ar, &loc, m, level),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Files.lean:396-413 readAllViews
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

/// con-leche: ConLeche/Frontend/Olean/Files.lean:396-413 readAllViews
/// **All three views of a module, each parsed whole, and their check against
/// each other** (`check_views`, over the views): for the tools that compare the
/// views.
pub fn read_all_views<F: OleanFs>(fs: &F, pk: &OleanPins, pers: &PersTier, ar: &mut EStore, sp: &Roots, m: &NIdx) -> Result<(AllViews, Vec<Expo>), CheckError> {
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

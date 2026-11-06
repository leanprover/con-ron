//! `olean_fs` — the `.olean` reader's file access over `std` (task #142).
//!
//! The core reads files through one trait, `con_ron_core::frontend::olean::files::
//! OleanFs`; this is the instance the binary runs, and all of it is outside the
//! theorems.  What a later hypothesis states of it (generalising `ReadsAs`, on one
//! snapshot of the files) is that it answers as a function of its arguments.

use con_ron_core::arena::handle::NIdx;
use con_ron_core::arena::monad;
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::store::PersTier;
use con_ron_core::frontend::export_c::ParseResultD;
use con_ron_core::frontend::olean::files;
use con_ron_core::frontend::olean::files::OleanFs;
use con_ron_core::frontend::olean::records;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::name::Name;

use crate::render;

/// con-leche: ConLeche/Frontend/CheckerIO.lean:449-461 instCheckerIOIO
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::StdFs_refines, then delete this line
/// **The binary's instance**: the runtime's calls.
pub struct StdFs;

/// con-leche: none — a path of the core as a Rust `String`
pub fn path_of(p: &[u32]) -> String {
    p.iter().filter_map(|c| char::from_u32(*c)).collect()
}

/// con-leche: none — a failed operation's message: the path and the error
fn io_msg(p: &str, e: std::io::Error) -> Vec<u32> {
    render::cps(&format!("{}: {}", render::display_path(p), e))
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:449-461 instCheckerIOIO
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::impl OleanFs for StdFs_refines, then delete this line
impl OleanFs for StdFs {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:117-159 CheckerIO
    /// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::path_exists_refines, then delete this line
    fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        Ok(std::path::Path::new(&path_of(p)).exists())
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:117-159 CheckerIO
    /// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::real_path_refines, then delete this line
    fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>> {
        let s = path_of(p);
        match std::fs::canonicalize(&s) {
            Ok(r) => Ok(render::cps(&r.to_string_lossy())),
            Err(e) => Err(io_msg(&s, e)),
        }
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:117-159 CheckerIO
    /// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::read_bin_file_refines, then delete this line
    fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>> {
        let s = path_of(p);
        std::fs::read(&s).map_err(|e| io_msg(&s, e))
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:330-341 readRangeOf
    /// A positional read: the bytes from `off` up to `off + len` or the end of the
    /// file.  The path must name a regular file.
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
        use std::os::unix::fs::FileExt;
        let s = path_of(p);
        let f = std::fs::File::open(&s).map_err(|e| io_msg(&s, e))?;
        let md = f.metadata().map_err(|e| io_msg(&s, e))?;
        if !md.is_file() {
            return Err(render::cps(&format!("{}: not a regular file", render::display_path(&s))));
        }
        let size = md.len();
        if off >= size {
            return Ok(Vec::new());
        }
        let want = std::cmp::min(len, size - off) as usize;
        let mut buf = vec![0u8; want];
        let mut got = 0usize;
        while got < want {
            match f.read_at(&mut buf[got..], off + got as u64) {
                Ok(0) => break,
                Ok(n) => got += n,
                Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(io_msg(&s, e)),
            }
        }
        buf.truncate(got);
        Ok(buf)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:449-461 instCheckerIOIO
    /// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::file_size_refines, then delete this line
    fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>> {
        let s = path_of(p);
        let md = std::fs::metadata(&s).map_err(|e| io_msg(&s, e))?;
        if md.is_file() {
            Ok(md.len())
        } else {
            Err(render::cps(&format!("{}: not a regular file", render::display_path(&s))))
        }
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:55-62 Input
/// What `--olean` asked for, the names parsed: a usage error is reported before
/// anything is read.
pub struct OleanRequest {
    pub search_path: Vec<Vec<u32>>,
    pub roots: Vec<Name>,
    pub constants: Vec<Name>,
}

/// con-leche: ConLeche/Driver/CheckMain.lean:64-67 Input.label
/// con-leche: ConLeche/Driver/Cli.lean:219-304 runArgs
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::impl OleanRequest_refines, then delete this line
impl OleanRequest {
    /// con-leche: ConLeche/Driver/Cli.lean:219-304 runArgs
    /// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::new_refines, then delete this line
    /// The names of the command line, or the usage error.
    pub fn new(search_path: &[String], modules: &[String], constants: &[String]) -> Result<OleanRequest, String> {
        let mut roots: Vec<Name> = Vec::new();
        for m in modules {
            match files::parse_mod_name(&render::cps(m)) {
                Some(n) => roots.push(n),
                None => return Err(format!("not a module name: {}", render::display_str(m))),
            }
        }
        let mut cs: Vec<Name> = Vec::new();
        for c in constants {
            match files::parse_const_name(&render::cps(c)) {
                Some(n) => cs.push(n),
                None => return Err(format!("not a constant's name: {}", render::display_str(c))),
            }
        }
        Ok(OleanRequest {
            search_path: search_path.iter().map(|d| render::cps(d)).collect(),
            roots,
            constants: cs,
        })
    }

    /// con-leche: ConLeche/Driver/CheckMain.lean:64-67 Input.label
    /// The input's name in a diagnostic.
    pub fn label(&self, _pers: &PersTier, _st: &AState) -> String {
        let shown: Vec<String> = self.roots.iter().map(|n| render::name_str(n)).collect();
        shown.join(" ")
    }

    /// con-leche: none — `a.rootConstants`, and `filterMap parseModName`, over handles
    /// The names, as handles.
    pub fn intern(&self, pers: &PersTier, st: &mut AState) -> Result<(Vec<NIdx>, Option<Vec<NIdx>>), CheckError> {
        let mut roots: Vec<NIdx> = Vec::with_capacity(self.roots.len());
        for n in &self.roots {
            roots.push(monad::intern_name(pers, st, n)?);
        }
        if self.constants.is_empty() {
            return Ok((roots, None));
        }
        let mut cs: Vec<NIdx> = Vec::with_capacity(self.constants.len());
        for n in &self.constants {
            cs.push(monad::intern_name(pers, st, n)?);
        }
        Ok((roots, Some(cs)))
    }
}

/// con-leche: ConLeche/Driver/CheckMain.lean:87-98 readInputG
/// con-leche: CHANGED since 7cb7a45c — re-port, re-test, re-prove olean_fs::read_request_refines, then delete this line
/// The input's declaration records, by the `.olean` reader.
pub fn read_request(pers: &PersTier, st: &mut AState, req: &OleanRequest) -> Result<ParseResultD, (CheckError, u64)> {
    let (roots, cs) = match req.intern(pers, st) {
        Ok(p) => p,
        Err(e) => return Err((e, 0)),
    };
    records::read_oleans(&StdFs, pers, &mut st.store, &req.search_path, &roots, &cs)
}

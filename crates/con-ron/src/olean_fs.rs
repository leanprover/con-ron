//! `olean_fs` — the `.olean` reader's file access over `std` (task #142).
//!
//! The core reads files through the file operations of the driver's trait,
//! `con_ron_core::frontend::checker_io::CheckerFs`; these are the binary's
//! (`std_io::StdIo` reads through [`RunFiles`], every path once per run; the
//! scheduler and `olean-compare` through [`StdFs`]), and all of it is outside
//! the theorems: that the operations a run performs answer as one snapshot is
//! OVERVIEW §3.1 (1).  Every byte read goes up to where a read finds the end of
//! the file, never to the size the metadata reports; a path with a code point
//! that is not a character fails (`fs_path`).
//!
//! Two instances: [`StdFs`], silent, for the check pool's workers reading a
//! theorem's value (`records::read_value`); and [`NotesFs`], the read's, which
//! also prints upstream's `read:` heartbeat (`ReadNotes`, task #484) at the pace
//! asked for, with the time since the read began and `VmRSS`.

use con_ron_core::frontend::checker_io::CheckerFs;
use con_ron_core::frontend::olean::progress;
use con_ron_core::frontend::pace;
use con_ron_core::frontend::pace::Pace;

use crate::render;

/// con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
/// **The binary's instance**: the runtime's calls.
pub struct StdFs;

/// con-leche: none — a path or a message of the core as a Rust `String`, for
/// display: a code point that is not a character is dropped.  The file
/// operations use `fs_path`, which fails there instead.
pub fn path_of(p: &[u32]) -> String {
    p.iter().filter_map(|c| char::from_u32(*c)).collect()
}

/// con-leche: none — **a path of the core as the file operations take it**: its
/// code points as a Rust `String`, or a failure where one is not a character
/// (the model's `Spelled`: a path that is not a well-formed string fails, so it
/// cannot name what a shorter spelling names).
pub fn fs_path(p: &[u32]) -> Result<String, Vec<u32>> {
    let mut s = String::with_capacity(p.len());
    for c in p {
        match char::from_u32(*c) {
            Some(ch) => s.push(ch),
            None => {
                return Err(render::cps(&format!(
                    "{}: not a path: the code point {:#x} is not a character",
                    render::display_path(&path_of(p)),
                    c
                )))
            }
        }
    }
    Ok(s)
}

/// con-leche: none — a failed operation's message: the path and the error
fn io_msg(p: &str, e: std::io::Error) -> Vec<u32> {
    render::cps(&format!("{}: {}", render::display_path(p), e))
}

/// con-leche: none — a failed operation's message: the path and what is wrong
fn path_msg(p: &str, what: &str) -> Vec<u32> {
    render::cps(&format!("{}: {}", render::display_path(p), what))
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:400-406 openReadIO
/// **A regular file, opened for reading**: the metadata says it is one before it
/// is opened (opening a FIFO with no writer would block), and the opened file's
/// again (the path may have changed in between).
pub fn open_regular(s: &str) -> Result<(std::fs::File, std::fs::Metadata), Vec<u32>> {
    match std::fs::metadata(s) {
        Err(e) => return Err(io_msg(s, e)),
        Ok(md) => {
            if !md.is_file() {
                return Err(path_msg(s, "not a regular file"));
            }
        }
    }
    let f = std::fs::File::open(s).map_err(|e| io_msg(s, e))?;
    let md = f.metadata().map_err(|e| io_msg(s, e))?;
    if !md.is_file() {
        return Err(path_msg(s, "not a regular file"));
    }
    Ok((f, md))
}

/// con-leche: none — **one positional read**: up to `buf.len()` bytes of `f` at
/// `off`, without moving a cursor other readers of the handle rely on.
#[cfg(unix)]
fn pread(f: &std::fs::File, buf: &mut [u8], off: u64) -> std::io::Result<usize> {
    use std::os::unix::fs::FileExt;
    f.read_at(buf, off)
}

/// con-leche: none — Windows' positional read (`seek_read` moves the handle's
/// cursor, which no reader here uses: every read names its offset).
#[cfg(windows)]
fn pread(f: &std::fs::File, buf: &mut [u8], off: u64) -> std::io::Result<usize> {
    use std::os::windows::fs::FileExt;
    f.seek_read(buf, off)
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:370-379 ModelIO.read
/// **A positional read of an open file**: the bytes from `off` up to `off + len`
/// or the end of the file, whichever comes first.  The end is where a read
/// answers nothing, not the size the metadata reports (a file of `/proc` reports
/// 0 and holds more); `len = None` reads to the end.
pub fn read_at_most(f: &std::fs::File, s: &str, off: u64, len: Option<u64>, hint: u64) -> Result<Vec<u8>, Vec<u32>> {
    let cap = match len {
        Some(l) => std::cmp::min(l, hint.saturating_sub(off)),
        None => hint.saturating_sub(off),
    };
    let mut buf: Vec<u8> = Vec::with_capacity(std::cmp::min(cap, 1 << 30) as usize);
    let mut chunk = vec![0u8; 1 << 16];
    loop {
        let got = buf.len() as u64;
        let want = match len {
            Some(l) if got >= l => break,
            Some(l) => std::cmp::min(l - got, chunk.len() as u64) as usize,
            None => chunk.len(),
        };
        match pread(f, &mut chunk[..want], off + got) {
            Ok(0) => break,
            Ok(n) => buf.extend_from_slice(&chunk[..n]),
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(e) => return Err(io_msg(s, e)),
        }
    }
    Ok(buf)
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:515-531 instCheckerIOIO
/// **The size of an open file**, checked against its contents: the metadata's
/// size, where the file's last byte is at `size - 1` and a read at `size`
/// answers nothing; a failure otherwise (a file of `/proc` or `/sys`, whose
/// metadata does not say how much it holds), so that the size, the positional
/// reads and the whole file's bytes are one file's.
pub fn checked_size(f: &std::fs::File, s: &str, md: &std::fs::Metadata) -> Result<u64, Vec<u32>> {
    let size = md.len();
    let past = read_at_most(f, s, size, Some(1), size)?;
    let last = if size > 0 { read_at_most(f, s, size - 1, Some(1), size)?.len() } else { 0 };
    if !past.is_empty() || (size > 0 && last != 1) {
        return Err(path_msg(s, "its size does not match its contents"));
    }
    Ok(size)
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
impl CheckerFs for StdFs {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        Ok(std::path::Path::new(&fs_path(p)?).exists())
    }
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// `System.FilePath.isDir`: through symbolic links, `false` where the path
    /// names nothing.
    fn is_dir(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        Ok(std::path::Path::new(&fs_path(p)?).is_dir())
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// A real path that is not valid UTF-8 fails: two such would otherwise be
    /// one string.
    fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>> {
        let s = fs_path(p)?;
        match std::fs::canonicalize(&s) {
            Ok(r) => match r.into_os_string().into_string() {
                Ok(t) => Ok(render::cps(&t)),
                Err(_) => Err(path_msg(&s, "its real path is not valid UTF-8")),
            },
            Err(e) => Err(io_msg(&s, e)),
        }
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// The bytes to the end of the file (`read_at_most`).
    fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>> {
        let s = fs_path(p)?;
        let (f, md) = open_regular(&s)?;
        read_at_most(&f, &s, 0, None, md.len())
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:400-406 openReadIO
    /// A positional read (`read_at_most`) of the regular file at the path, on a
    /// handle of this call's own.
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
        let s = fs_path(p)?;
        let (f, md) = open_regular(&s)?;
        read_at_most(&f, &s, off, Some(len), md.len())
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
    /// The size, checked against the contents (`checked_size`).
    fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>> {
        let s = fs_path(p)?;
        let (f, md) = open_regular(&s)?;
        checked_size(&f, &s, &md)
    }

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:42-48 ReadNotes.say
    /// Silent: a worker's reads have no heartbeat.
    fn read_notes_say(&self, _line: &Vec<u32>) {}

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:50-60 ReadNotes.moduleLoaded
    /// Silent.
    fn read_notes_module_loaded(&self, _total: u64, _size: u64) {}
}

/// con-leche: none — **what identifies the file a run read at a path**: its
/// device, its inode, its size and its modification time when first opened.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Stamp {
    dev: u64,
    ino: u64,
    len: u64,
    mtime: i64,
    mtime_ns: i64,
}

/// con-leche: none — the stamp of an opened file's metadata
#[cfg(unix)]
fn stamp_of(md: &std::fs::Metadata) -> Stamp {
    use std::os::unix::fs::MetadataExt;
    Stamp { dev: md.dev(), ino: md.ino(), len: md.len(), mtime: md.mtime(), mtime_ns: md.mtime_nsec() }
}

/// con-leche: none — the stamp off Unix: no device or inode on stable Rust
/// (Windows' volume serial and file index are unstable), so `0` for both, and
/// only the size and the modification time tell a replaced file apart.
#[cfg(not(unix))]
fn stamp_of(md: &std::fs::Metadata) -> Stamp {
    let t = md.modified().ok().and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok()).unwrap_or_default();
    Stamp { dev: 0, ino: 0, len: md.len(), mtime: t.as_secs() as i64, mtime_ns: t.subsec_nanos() as i64 }
}

/// con-leche: none — a path the run has opened: the file's stamp, and its
/// handle while it is among the open ones
struct Seen {
    stamp: Stamp,
    file: Option<std::sync::Arc<std::fs::File>>,
}

/// con-leche: none — how many handles a run keeps open at once
const OPEN_CAP: usize = 256;

/// con-leche: ConLeche/Frontend/CheckerIO.lean:302-304 HS
/// **The files of one run**, by path (`StdIo`'s reads): each path is opened
/// once and read through that handle, so every read of it within the run is
/// one file's, even if the path is replaced meanwhile.  At most `OPEN_CAP`
/// handles stay open (a closure of thousands of modules against the usual 1024
/// open files): a path whose handle was closed is opened again and must be the
/// file it was (`Stamp`: the same device, inode, size and modification time),
/// or the read fails.
pub struct RunFiles {
    seen: std::sync::Mutex<(std::collections::HashMap<String, Seen>, std::collections::VecDeque<String>)>,
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:302-304 HS
impl RunFiles {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:302-304 HS
    /// No file opened yet.
    pub fn new() -> RunFiles {
        RunFiles { seen: std::sync::Mutex::new((std::collections::HashMap::new(), std::collections::VecDeque::new())) }
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:400-406 openReadIO
    /// **The run's handle of the regular file at `s`**, and its metadata when the
    /// run first opened it.
    fn open(&self, s: &str) -> Result<(std::sync::Arc<std::fs::File>, std::fs::Metadata), Vec<u32>> {
        {
            let g = self.seen.lock().map_err(|_| path_msg(s, "the run's open files are lost"))?;
            if let Some(Seen { file: Some(f), .. }) = g.0.get(s) {
                let f = f.clone();
                drop(g);
                let md = f.metadata().map_err(|e| io_msg(s, e))?;
                return Ok((f, md));
            }
        }
        let (f, md) = open_regular(s)?;
        let st = stamp_of(&md);
        let f = std::sync::Arc::new(f);
        let mut g = self.seen.lock().map_err(|_| path_msg(s, "the run's open files are lost"))?;
        let (map, order) = &mut *g;
        match map.get_mut(s) {
            Some(seen) => {
                if seen.stamp != st {
                    return Err(path_msg(s, "replaced or changed during the run"));
                }
                if let Some(f0) = &seen.file {
                    // another thread opened it meanwhile: read through that one
                    let f0 = f0.clone();
                    return Ok((f0, md));
                }
                seen.file = Some(f.clone());
            }
            None => {
                map.insert(s.to_string(), Seen { stamp: st, file: Some(f.clone()) });
            }
        }
        order.push_back(s.to_string());
        while order.len() > OPEN_CAP {
            if let Some(old) = order.pop_front() {
                if let Some(seen) = map.get_mut(&old) {
                    seen.file = None;
                }
            }
        }
        Ok((f, md))
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:370-379 ModelIO.read
    /// A positional read through the run's handle (`read_at_most`).
    pub fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
        let s = fs_path(p)?;
        let (f, md) = self.open(&s)?;
        read_at_most(&f, &s, off, Some(len), md.len())
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// The bytes to the end of the file, through the run's handle.
    pub fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>> {
        let s = fs_path(p)?;
        let (f, md) = self.open(&s)?;
        read_at_most(&f, &s, 0, None, md.len())
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
    /// The size, checked against the contents, through the run's handle.
    pub fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>> {
        let s = fs_path(p)?;
        let (f, md) = self.open(&s)?;
        checked_size(&f, &s, &md)
    }
}

/// con-leche: ConLeche/Frontend/Olean/Progress.lean:18-25 ReadNotes
/// **The read's instance**: `StdFs`'s reads and the heartbeat of one read: the
/// pace, when the read began, the modules and constants loaded so far, and when
/// the last line was.
pub struct NotesFs {
    pub pace: Pace,
    pub t0: std::time::Instant,
    pub loaded: std::sync::Mutex<(u64, u64)>,
    pub last: std::sync::Mutex<std::time::Instant>,
}

/// con-leche: ConLeche/Frontend/Olean/Progress.lean:27-28 ReadNotes.new
/// The notes of a read beginning now (`Pace.clock` is now too).
pub fn read_notes_new(pace: &Pace) -> NotesFs {
    let now = std::time::Instant::now();
    NotesFs { pace: pace::pace_dup(pace), t0: now, loaded: std::sync::Mutex::new((0, 0)), last: std::sync::Mutex::new(now) }
}

/// con-leche: ConLeche/Frontend/Olean/Progress.lean:30-40 residentSet
/// The resident set, in the kernel's words; empty where it cannot be read.
pub fn resident_set() -> Vec<u32> {
    let s = match std::fs::read_to_string("/proc/self/status") {
        Ok(s) => s,
        Err(_) => return Vec::new(),
    };
    for l in s.lines() {
        if let Some(rest) = l.strip_prefix("VmRSS:") {
            let digits: String = rest.trim().chars().take_while(|c| c.is_ascii_digit()).collect();
            return progress::rss_text(digits.parse::<u64>().unwrap_or(0));
        }
    }
    Vec::new()
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
/// `StdFs`'s reads; the heartbeat's two actions print.
impl CheckerFs for NotesFs {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        StdFs.path_exists(p)
    }
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn is_dir(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        StdFs.is_dir(p)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>> {
        StdFs.real_path(p)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>> {
        StdFs.read_bin_file(p)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
        StdFs.read_range(p, off, len)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>> {
        StdFs.file_size(p)
    }

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:42-48 ReadNotes.say
    /// One line of the heartbeat, on stderr: `con-ron: read: <line> t=<s>s RSS=<g>G`.
    fn read_notes_say(&self, line: &Vec<u32>) {
        use std::io::Write;
        if pace::pace_on(&self.pace) {
            let ms = self.t0.elapsed().as_millis() as u64;
            let text = progress::read_line_text(line, ms, &resident_set());
            let shown: String = text.iter().filter_map(|c| char::from_u32(*c)).collect();
            let mut e = std::io::stderr().lock();
            let _ = writeln!(e, "con-ron: {}", shown);
            let _ = e.flush();
        }
    }

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:50-60 ReadNotes.moduleLoaded
    /// A module of `total` is loaded, with `size` constants: a line when one is
    /// due (`progress::module_loaded_due_count`; the clock arm here).
    fn read_notes_module_loaded(&self, total: u64, size: u64) {
        if !pace::pace_on(&self.pace) {
            return;
        }
        let (k, c) = {
            let mut g = self.loaded.lock().unwrap_or_else(|p| p.into_inner());
            *g = (g.0 + 1, g.1 + size);
            *g
        };
        let due = match &self.pace {
            Pace::Seconds(sec) => {
                let now = std::time::Instant::now();
                let mut last = self.last.lock().unwrap_or_else(|p| p.into_inner());
                if now.duration_since(*last).as_millis() as u64 >= sec.saturating_mul(1000) {
                    *last = now;
                    true
                } else {
                    false
                }
            }
            p => progress::module_loaded_due_count(p, k, c, size, total),
        };
        if due {
            self.read_notes_say(&progress::module_loaded_text(k, c, total));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cps(s: &str) -> Vec<u32> {
        s.chars().map(|c| c as u32).collect()
    }

    /// A path with a code point that is not a character fails every operation.
    #[test]
    fn invalid_code_point_fails() {
        let mut p = cps("/tmp");
        p.push(0x110000);
        assert!(fs_path(&p).is_err());
        assert!(StdFs.path_exists(&p).is_err());
        assert!(StdFs.real_path(&p).is_err());
        assert!(RunFiles::new().read_range(&p, 0, 10).is_err());
    }

    /// A file whose metadata reports no size: the reads find its bytes, the
    /// size fails.
    #[test]
    fn proc_file_reads_to_its_end() {
        let p = cps("/proc/version");
        if std::fs::metadata("/proc/version").map(|m| m.len() != 0).unwrap_or(true) {
            return;
        }
        let rf = RunFiles::new();
        let whole = rf.read_bin_file(&p).unwrap();
        assert!(!whole.is_empty());
        assert_eq!(rf.read_range(&p, 0, 1 << 20).unwrap(), whole);
        assert!(rf.file_size(&p).is_err());
        assert_eq!(StdFs.read_range(&p, 0, 1 << 20).unwrap(), whole);
    }

    /// A file replaced during a run: its reads are the first file's, through
    /// the run's handle; once the handle is closed, a read fails.
    #[test]
    fn replaced_file_is_not_spliced() {
        let dir = std::env::temp_dir().join(format!("con-ron-runfiles-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("a.bin");
        std::fs::write(&f, b"0123456789").unwrap();
        let p = cps(f.to_str().unwrap());
        let rf = RunFiles::new();
        assert_eq!(rf.read_range(&p, 0, 4).unwrap(), b"0123");
        assert_eq!(rf.file_size(&p).unwrap(), 10);
        let g = dir.join("b.bin");
        std::fs::write(&g, b"abcdefghijklmnop").unwrap();
        std::fs::rename(&g, &f).unwrap();
        assert_eq!(rf.read_range(&p, 4, 100).unwrap(), b"456789");
        assert_eq!(rf.read_bin_file(&p).unwrap(), b"0123456789");
        // close every handle: the path is opened again, and is another file
        for i in 0..OPEN_CAP {
            let h = dir.join(format!("h{}", i));
            std::fs::write(&h, b"x").unwrap();
            rf.read_range(&cps(h.to_str().unwrap()), 0, 1).unwrap();
        }
        assert!(rf.read_range(&p, 0, 4).is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }
}

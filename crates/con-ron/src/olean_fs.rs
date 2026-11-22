//! `olean_fs` — the `.olean` reader's file access over `std` (task #142).
//!
//! The core reads files through the file operations of the driver's trait,
//! `con_ron_core::frontend::checker_io::CheckerFs`; these are the binary's
//! (`std_io::StdIo`'s operations are these, and so are the scheduler's and
//! `olean-compare`'s), and all of it is outside the theorems: that they answer
//! as one snapshot is OVERVIEW §3.1's `AnswersAs`.
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

/// con-leche: none — a path of the core as a Rust `String`
pub fn path_of(p: &[u32]) -> String {
    p.iter().filter_map(|c| char::from_u32(*c)).collect()
}

/// con-leche: none — a failed operation's message: the path and the error
fn io_msg(p: &str, e: std::io::Error) -> Vec<u32> {
    render::cps(&format!("{}: {}", render::display_path(p), e))
}

/// con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
impl CheckerFs for StdFs {
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        Ok(std::path::Path::new(&path_of(p)).exists())
    }
    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    /// `System.FilePath.isDir`: through symbolic links, `false` where the path
    /// names nothing.
    fn is_dir(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        Ok(std::path::Path::new(&path_of(p)).is_dir())
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>> {
        let s = path_of(p);
        match std::fs::canonicalize(&s) {
            Ok(r) => Ok(render::cps(&r.to_string_lossy())),
            Err(e) => Err(io_msg(&s, e)),
        }
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:137-184 CheckerIO
    fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>> {
        let s = path_of(p);
        std::fs::read(&s).map_err(|e| io_msg(&s, e))
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:400-406 openReadIO
    /// A positional read: the bytes from `off` up to `off + len` or the end of the
    /// file.  The path must name a regular file, as `openReadIO` checks; then a
    /// seek to `off` and forward reads on a handle of this call's own, so no other
    /// reader shares its position (portable: no `FileExt::read_at`, which is
    /// Unix-only).
    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
        use std::io::{Read, Seek, SeekFrom};
        let s = path_of(p);
        let mut f = std::fs::File::open(&s).map_err(|e| io_msg(&s, e))?;
        let md = f.metadata().map_err(|e| io_msg(&s, e))?;
        if !md.is_file() {
            return Err(render::cps(&format!("{}: not a regular file", render::display_path(&s))));
        }
        let size = md.len();
        if off >= size {
            return Ok(Vec::new());
        }
        let want = std::cmp::min(len, size - off) as usize;
        f.seek(SeekFrom::Start(off)).map_err(|e| io_msg(&s, e))?;
        let mut buf = vec![0u8; want];
        let mut got = 0usize;
        while got < want {
            match f.read(&mut buf[got..]) {
                Ok(0) => break,
                Ok(n) => got += n,
                Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => {}
                Err(e) => return Err(io_msg(&s, e)),
            }
        }
        buf.truncate(got);
        Ok(buf)
    }

    /// con-leche: ConLeche/Frontend/CheckerIO.lean:514-529 instCheckerIOIO
    fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>> {
        let s = path_of(p);
        let md = std::fs::metadata(&s).map_err(|e| io_msg(&s, e))?;
        if md.is_file() {
            Ok(md.len())
        } else {
            Err(render::cps(&format!("{}: not a regular file", render::display_path(&s))))
        }
    }

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:42-48 ReadNotes.say
    /// Silent: a worker's reads have no heartbeat.
    fn read_notes_say(&self, _line: &Vec<u32>) {}

    /// con-leche: ConLeche/Frontend/Olean/Progress.lean:50-60 ReadNotes.moduleLoaded
    /// Silent.
    fn read_notes_module_loaded(&self, _total: u64, _size: u64) {}
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

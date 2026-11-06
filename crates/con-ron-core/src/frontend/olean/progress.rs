//! `ConLeche/Frontend/Olean/Progress.lean` — what `--progress` says while the
//! `.olean` files are read (upstream task #484), its pure part.
//!
//! The read's heartbeat: a line per step of `readOleans`, and during the load
//! lines at `--progress`'s pace, each with the time and the resident set.
//! `ReadNotes` and its actions are `IO` (the clock, `/proc/self/status`,
//! stderr): they are the driver's, `crates/con-ron`'s `olean_fs`, which
//! reaches them through the file seam (`files::OleanFs::read_notes_say`,
//! `read_notes_module_loaded`).  What is here is their arithmetic and their
//! text, so that the lines are upstream's.
//!
//! Deviation: the line's prefix (`con-leche: `) is the driver's, which prints
//! its own program name.

use crate::frontend::pace;
use crate::frontend::pace::Pace;
use crate::frontend::text;

/// con-leche: ConLeche/Frontend/Olean/Progress.lean:30-40 residentSet
/// The resident set's text from `VmRSS`'s kibibytes: ` RSS=<x>.<yz>G`.
pub fn rss_text(kb: u64) -> Vec<u32> {
    let x = pace::sat_mul(kb, 100) / 1048576;
    let s = text::cat({ const M: [u32; 5] = [32, 82, 83, 83, 61]; crate::kernel::core_types::code_points(&M) }, &text::u64_str(x / 100));
    let s = text::cat(s, &{ const M: [u32; 1] = [46]; crate::kernel::core_types::code_points(&M) });
    let s = text::cat(s, &text::u64_str((x % 100) / 10));
    let s = text::cat(s, &text::u64_str(x % 10));
    text::cat(s, &{ const M: [u32; 1] = [71]; crate::kernel::core_types::code_points(&M) })
}

/// con-leche: ConLeche/Frontend/Olean/Progress.lean:42-48 ReadNotes.say
/// One line of the heartbeat after the prefix: `read: <line> t=<s>.<d>s<rss>`,
/// `ms` the milliseconds since the read began.
pub fn read_line_text(line: &Vec<u32>, ms: u64, rss: &Vec<u32>) -> Vec<u32> {
    let s = text::cat({ const M: [u32; 6] = [114, 101, 97, 100, 58, 32]; crate::kernel::core_types::code_points(&M) }, line);
    let s = text::cat(s, &{ const M: [u32; 3] = [32, 116, 61]; crate::kernel::core_types::code_points(&M) });
    let s = text::cat(s, &text::u64_str(ms / 1000));
    let s = text::cat(s, &{ const M: [u32; 1] = [46]; crate::kernel::core_types::code_points(&M) });
    let s = text::cat(s, &text::u64_str((ms % 1000) / 100));
    let s = text::cat(s, &{ const M: [u32; 1] = [115]; crate::kernel::core_types::code_points(&M) });
    text::cat(s, rss)
}

/// con-leche: ConLeche/Frontend/Olean/Progress.lean:50-60 ReadNotes.moduleLoaded
/// **Is a line due** once module `k` of `total` is loaded, `c` constants so far,
/// `size` of them this module's: at `.every m` a line per `m` constants, at a
/// percentage by modules; `false` at `.seconds`, whose clock arm is the driver's.
pub fn module_loaded_due_count(p: &Pace, k: u64, c: u64, size: u64, total: u64) -> bool {
    match p {
        Pace::Every(m) => {
            let before = if c >= size { c - size } else { 0 };
            *m > 0 && c / *m != before / *m
        }
        _ => pace::pace_due_count(p, k, total),
    }
}

/// con-leche: ConLeche/Frontend/Olean/Progress.lean:50-60 ReadNotes.moduleLoaded
/// The line: `loaded <k> modules (<k*100/total>%), <c> constants`.
pub fn module_loaded_text(k: u64, c: u64, total: u64) -> Vec<u32> {
    let t = if total > 1 { total } else { 1 };
    let s = text::cat({ const M: [u32; 7] = [108, 111, 97, 100, 101, 100, 32]; crate::kernel::core_types::code_points(&M) }, &text::u64_str(k));
    let s = text::cat(s, &{ const M: [u32; 10] = [32, 109, 111, 100, 117, 108, 101, 115, 32, 40]; crate::kernel::core_types::code_points(&M) });
    let s = text::cat(s, &text::u64_str(pace::sat_mul(k, 100) / t));
    let s = text::cat(s, &{ const M: [u32; 4] = [37, 41, 44, 32]; crate::kernel::core_types::code_points(&M) });
    let s = text::cat(s, &text::u64_str(c));
    text::cat(s, &{ const M: [u32; 10] = [32, 99, 111, 110, 115, 116, 97, 110, 116, 115]; crate::kernel::core_types::code_points(&M) })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(v: &[u32]) -> String {
        v.iter().filter_map(|c| char::from_u32(*c)).collect()
    }

    #[test]
    fn the_lines_are_upstreams() {
        assert_eq!(s(&rss_text(3 * 1048576 + 524288)), " RSS=3.50G");
        assert_eq!(s(&read_line_text(&"x".chars().map(|c| c as u32).collect(), 12345, &Vec::new())), "read: x t=12.3s");
        assert_eq!(s(&module_loaded_text(3, 70, 10)), "loaded 3 modules (30%), 70 constants");
        assert!(module_loaded_due_count(&Pace::Every(100), 2, 120, 30, 10));
        assert!(!module_loaded_due_count(&Pace::Every(100), 2, 130, 10, 10));
    }
}

//! Rendering for a human: the CLI's receipts, the modeller's decline
//! messages, the trace lines, the usage errors.  No con-leche file of its own.
//!
//! The rendering itself is the verified core's port of con-leche's display
//! rendering (`con_ron_core::kernel::name::render` and `display_str`,
//! `ConLeche/Kernel/Name.lean`), which escapes every control, format and
//! separator character an input name or string carries.  It returns the
//! port's `Vec<u32>` of code points, because that is what a `CheckError`
//! holds; this crate writes to a terminal, so it wants a Rust `String`, and
//! this is the one place the two meet.

use con_ron_core::kernel::name;
use con_ron_core::kernel::name::Name;

/// con-leche: none — `toString n` (`Name.render`) as a Rust `String`
/// The core's `name::render`, converted.  Every code point it returns is a
/// Unicode scalar value (`display_unsafe_char` escapes the others).
pub fn name_str(n: &Name) -> String {
    from_cps(&name::render(n))
}

/// con-leche: none — `Display.str s` as a Rust `String`
/// The core's `name::display_str` of a command-line word: between `"`…`"`,
/// escaped and capped.
pub fn display_str(s: &str) -> String {
    from_cps(&name::display_str(&cps(s)))
}

/// con-leche: none — con-leche prints a path from the command line raw
/// A file path from the command line, for a message: as it is when it holds
/// nothing a display must escape, else `display_str` of it.  Deviation from
/// con-leche, which prints `{file}` raw (task #131): a path is the caller's
/// own word, but a script can pass one it did not choose (a file name from an
/// archive), so it gets the same guarantee as the input.  An ordinary path
/// prints exactly as con-leche prints it.
pub fn display_path(s: &str) -> String {
    let plain = s
        .chars()
        .all(|c| c != '\\' && c != '"' && !name::display_unsafe_char(c as u32));
    if plain {
        s.to_string()
    } else {
        display_str(s)
    }
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code
/// points (DESIGN.md §3.3); a driver message on its way into a `CheckError`.
pub fn cps(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

/// con-leche: none — `cps`'s reverse, a code-point string as a Rust `String`
fn from_cps(s: &[u32]) -> String {
    s.iter().filter_map(|c| char::from_u32(*c)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn names_render_escaped() {
        let nat = name::mk_str(name::anonymous(), cps("Nat"));
        let succ = name::mk_str(name::dup(&nat), cps("succ"));
        let idx = name::mk_num(name::dup(&succ), 3);
        assert_eq!(name_str(&name::anonymous()), "[anonymous]");
        assert_eq!(name_str(&idx), "Nat.succ.3");
        let evil = name::mk_str(succ, cps("a\u{1b}[2K\r"));
        assert_eq!(name_str(&evil), "Nat.succ.\u{ab}a\\u{001B}[2K\\u{000D}\u{bb}");
    }

    #[test]
    fn words_render_quoted() {
        assert_eq!(display_str("x"), "\"x\"");
        assert_eq!(display_str("\u{1b}"), "\"\\u{001B}\"");
    }

    #[test]
    fn paths_render_raw_unless_hostile() {
        assert_eq!(display_path("tests/e2e/a b.ndjson"), "tests/e2e/a b.ndjson");
        assert_eq!(display_path("x\u{1b}[2Ky\n::error::z"), "\"x\\u{001B}[2Ky\\u{000A}::error::z\"");
        assert_eq!(display_path("a\\b"), "\"a\\\\b\"");
        assert_eq!(display_path("a\u{202e}b"), "\"a\\u{202E}b\"");
    }

    #[test]
    fn cps_round_trips() {
        for s in ["", "Nat.succ", "\u{3b1}\u{3b2}", "[anonymous]"] {
            assert_eq!(from_cps(&cps(s)), s);
        }
    }
}

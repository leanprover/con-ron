//! Rendering a `Name` for a human: the CLI's receipts, the modeller's decline
//! messages, the trace lines.  No con-leche file of its own.
//!
//! `Name.toString` is on DESIGN.md §3.7's skip list — driver-only rendering,
//! "the theorem never reads a message" — so the verified core does not port
//! it, and what the core *does* carry
//! (`con_ron_core::frontend::text::name_str`) returns the port's `Vec<u32>`
//! of code points, because that is what a `CheckError` holds.  This crate
//! writes to a terminal, so it wants a Rust `String`; this is the one place
//! the two meet.
//!
//! Before task #84 this function lived in `crate::frontend::export`, beside
//! the parser.  The parser is in the verified core now and cannot have it.

use con_ron_core::kernel::name::{Name, NameKind};

/// con-leche: none — `Name.toString`, which DESIGN.md §3.7's skip list keeps
/// out of the verified core as driver-only rendering.  `anonymous` is
/// `[anonymous]`, and a component is appended after a dot.
pub fn name_str(n: &Name) -> String {
    match &n.0.kind {
        NameKind::Anonymous => "[anonymous]".to_string(),
        NameKind::Str(p, s) => {
            let tail: String = s.iter().filter_map(|c| char::from_u32(*c)).collect();
            match &p.0.kind {
                NameKind::Anonymous => tail,
                _ => format!("{}.{}", name_str(p), tail),
            }
        }
        NameKind::Num(p, k) => match &p.0.kind {
            NameKind::Anonymous => format!("{}", k),
            _ => format!("{}.{}", name_str(p), k),
        },
    }
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code
/// points (DESIGN.md §3.3); this is the reverse, at the boundary where a
/// `CheckError`'s message becomes a line on stderr.
pub fn from_cps(s: &[u32]) -> String {
    s.iter().filter_map(|c| char::from_u32(*c)).collect()
}

/// con-leche: none — the port stores every Lean `String` as `Vec<u32>` code
/// points (DESIGN.md §3.3); a driver message on its way into a `CheckError`.
pub fn cps(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::kernel::name;

    #[test]
    fn the_two_renderings_agree() {
        let nat = name::mk_str(name::anonymous(), cps("Nat"));
        let succ = name::mk_str(name::dup(&nat), cps("succ"));
        let idx = name::mk_num(name::dup(&succ), 3);
        for n in [name::anonymous(), nat, succ, idx] {
            assert_eq!(
                name_str(&n),
                from_cps(&con_ron_core::frontend::text::name_str(&n))
            );
        }
    }

    #[test]
    fn cps_round_trips() {
        for s in ["", "Nat.succ", "\u{3b1}\u{3b2}", "[anonymous]"] {
            assert_eq!(from_cps(&cps(s)), s);
        }
    }
}

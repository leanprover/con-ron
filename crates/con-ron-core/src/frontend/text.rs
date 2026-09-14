//! The parser's message rendering: no Lean file of its own.
//!
//! con-leche builds its frontend messages with string interpolation
//! (`s!"… {n} …"`), over Lean `String`s.  The core stores every Lean `String`
//! as a `Vec<u32>` of code points (DESIGN.md §3.3), and `format!` is outside
//! the Aeneas subset (§3.4), so the three things the interpolations actually
//! do — append, render a number, render a `Name` — are three functions here
//! and every message in `frontend/` is built out of them.
//!
//! Nothing in this module is on a *verdict* path: a message decides no exit
//! code (the differential compares exit codes, `OVERVIEW.md` §5.4).  It is
//! here rather than in the unverified crate because the messages travel
//! inside `CheckError`, which the parse now returns from the verified core.

use crate::kernel::name::{Name, NameKind};

/// con-leche: none — Lean's `s!"{a}{b}"` on two `String`s
/// Append `b` to `a`.  The accumulator is passed by value and returned
/// (DESIGN.md §3.4 reserves `&mut` for the state parameter).
pub fn cat(a: Vec<u32>, b: &Vec<u32>) -> Vec<u32> {
    let mut out = a;
    let n = b.len();
    let mut i = 0usize;
    while i < n {
        out.push(b[i]);
        i += 1;
    }
    out
}

/// con-leche: none — Lean's `s!"{a}{b}{c}"` on three `String`s
pub fn cat3(a: Vec<u32>, b: &Vec<u32>, c: &Vec<u32>) -> Vec<u32> {
    cat(cat(a, b), c)
}

/// con-leche: none — Lean's `s!"{n}"` on a `Nat`
/// The decimal digits of `n`, most significant first.  At most twenty digits,
/// so the reversal is a bounded loop.
pub fn u64_str(n: u64) -> Vec<u32> {
    if n == 0 {
        let mut z: Vec<u32> = Vec::new();
        z.push(48);
        return z;
    }
    let mut rev: Vec<u32> = Vec::new();
    let mut k = n;
    while k > 0 {
        rev.push(48 + ((k % 10) as u32));
        k = k / 10;
    }
    let mut out: Vec<u32> = Vec::with_capacity(rev.len());
    let mut i = rev.len();
    while i > 0 {
        i -= 1;
        out.push(rev[i]);
    }
    out
}

/// con-leche: none — `Name.toString`, which DESIGN.md §3.7's skip list keeps
/// out of the ported checker as driver-only rendering ("the theorem never
/// reads a message").  The parse's own messages name declarations, so the
/// rendering has to be here: `anonymous` is `[anonymous]`, and a component is
/// appended after a dot.
pub fn name_str(n: &Name) -> Vec<u32> {
    match &n.0.kind {
        NameKind::Anonymous => {
            const A: [u32; 11] = [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93];
            crate::kernel::core_types::code_points(&A)
        }
        NameKind::Str(p, s) => match &p.0.kind {
            NameKind::Anonymous => cat(Vec::new(), s),
            _ => {
                const DOT: [u32; 1] = [46];
                cat3(
                    name_str(p),
                    &crate::kernel::core_types::code_points(&DOT),
                    s,
                )
            }
        },
        NameKind::Num(p, k) => match &p.0.kind {
            NameKind::Anonymous => u64_str(*k),
            _ => {
                const DOT: [u32; 1] = [46];
                cat3(
                    name_str(p),
                    &crate::kernel::core_types::code_points(&DOT),
                    &u64_str(*k),
                )
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::name;

    fn s(v: &[u32]) -> String {
        v.iter().filter_map(|c| char::from_u32(*c)).collect()
    }

    fn cp(t: &str) -> Vec<u32> {
        t.chars().map(|c| c as u32).collect()
    }

    #[test]
    fn u64_str_is_decimal() {
        assert_eq!(s(&u64_str(0)), "0");
        assert_eq!(s(&u64_str(7)), "7");
        assert_eq!(s(&u64_str(10)), "10");
        assert_eq!(s(&u64_str(1234567890)), "1234567890");
        assert_eq!(s(&u64_str(u64::MAX)), "18446744073709551615");
    }

    #[test]
    fn cat_appends() {
        assert_eq!(s(&cat(cp("ab"), &cp("cd"))), "abcd");
        assert_eq!(s(&cat3(cp("a"), &cp("b"), &cp("c"))), "abc");
        assert_eq!(s(&cat(Vec::new(), &cp(""))), "");
    }

    #[test]
    fn name_str_is_the_dotted_name() {
        let a = name::anonymous();
        assert_eq!(s(&name_str(&a)), "[anonymous]");
        let nat = name::mk_str(name::anonymous(), cp("Nat"));
        assert_eq!(s(&name_str(&nat)), "Nat");
        let succ = name::mk_str(name::dup(&nat), cp("succ"));
        assert_eq!(s(&name_str(&succ)), "Nat.succ");
        let idx = name::mk_num(name::dup(&succ), 3);
        assert_eq!(s(&name_str(&idx)), "Nat.succ.3");
        let bare = name::mk_num(name::anonymous(), 12);
        assert_eq!(s(&name_str(&bare)), "12");
    }
}

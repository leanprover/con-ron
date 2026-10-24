//! The parser's message rendering: no Lean file of its own.
//!
//! con-leche builds its frontend messages with string interpolation
//! (`s!"… {n} …"`), over Lean `String`s.  The core stores every Lean `String`
//! as a `Vec<u32>` of code points (DESIGN.md §3.3), and `format!` is outside
//! the Aeneas subset (§3.4), so what the interpolations actually do — append,
//! render a number — is here, and every message in `frontend/` is built out
//! of it and of `kernel::name::render`/`display_str`, the display rendering
//! of a name and of a raw input string.
//!
//! Nothing in this module is on a *verdict* path: a message decides no exit
//! code (the differential compares exit codes, `OVERVIEW.md` §10).  It is
//! here rather than in the unverified crate because the messages travel
//! inside `CheckError`, which the parse now returns from the verified core.

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

/// con-leche: none — `String`'s `BEq` on the port's code-point representation
/// Whether a code-point string is the literal `lit` (a `const …: [u32; N]`).
/// This is how the parse compares a stream's `safety` or `kind` spelling with
/// a word of the dialect without materialising the literal as a `Vec`.
pub fn cps_beq(s: &Vec<u32>, lit: &[u32]) -> bool {
    if s.len() != lit.len() {
        return false;
    }
    let n = s.len();
    let mut i = 0usize;
    while i < n {
        if s[i] != lit[i] {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: none — `String.startsWith` on the port's code-point representation
/// Whether the code-point string `s` begins with the literal `lit` (a
/// `const …: [u32; N]`), without materialising the literal as a `Vec`.
pub fn cps_starts_with(s: &Vec<u32>, lit: &[u32]) -> bool {
    if s.len() < lit.len() {
        return false;
    }
    let n = lit.len();
    let mut i = 0usize;
    while i < n {
        if s[i] != lit[i] {
            return false;
        }
        i += 1;
    }
    true
}


#[cfg(test)]
mod tests {
    use super::*;

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
    fn cps_starts_with_is_a_prefix_test() {
        assert!(cps_starts_with(&cp("ax_1_1"), &[97, 120]));
        assert!(cps_starts_with(&cp("ax"), &[97, 120]));
        assert!(!cps_starts_with(&cp("a"), &[97, 120]));
        assert!(!cps_starts_with(&cp("decl_1"), &[97, 120]));
        assert!(cps_starts_with(&cp(""), &[]));
    }
}

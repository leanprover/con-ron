//! `ConLeche/Frontend/Pace.lean` — how often `--progress` says something (task
//! #484), its pure part.
//!
//! `--progress[=N|P%|Ss]`: a line every `N` items, per `P` percent of a phase's
//! items, or at the first item done once `S` seconds have passed since the last
//! line.  Only the heartbeat reads this: no verdict does.
//!
//! ## Deviations
//!
//! * `Pace.clock` and the `.seconds` arm of `Pace.due` read the clock, an `IO`
//!   action: they are the driver's (`crates/con-ron`), outside the core.  The
//!   rest of `Pace.due` is [`pace_due_count`], which answers `false` at
//!   `.seconds`.
//! * `Nat` is `u64`; `p * total` saturates and `k - 1` is `Nat`'s truncated
//!   subtraction.

/// con-leche: ConLeche/Frontend/Pace.lean:16-22 Pace
/// How often the heartbeat speaks.
pub enum Pace {
    Off,
    Every(u64),
    Percent(u64),
    Seconds(u64),
}

/// con-leche: ConLeche/Frontend/Pace.lean:16-22 Pace
/// The record copy (`deriving` is not in the subset, DESIGN.md §3.4).
pub fn pace_dup(p: &Pace) -> Pace {
    match p {
        Pace::Off => Pace::Off,
        Pace::Every(n) => Pace::Every(*n),
        Pace::Percent(n) => Pace::Percent(*n),
        Pace::Seconds(n) => Pace::Seconds(*n),
    }
}

/// con-leche: ConLeche/Frontend/Pace.lean:24-27 Pace.on
/// Does the heartbeat speak at all?
pub fn pace_on(p: &Pace) -> bool {
    match p {
        Pace::Off => false,
        _ => true,
    }
}

/// con-leche: ConLeche/Frontend/Pace.lean:29-33 Pace.trace
/// Does the heartbeat speak at every item?  Then it is a trace, and a line names
/// its item.
pub fn pace_trace(p: &Pace) -> bool {
    match p {
        Pace::Every(n) => *n == 1,
        _ => false,
    }
}

/// con-leche: none — `Nat`'s `*`, stopping at `u64::MAX` (module note)
#[inline(always)]
pub fn sat_mul(a: u64, b: u64) -> u64 {
    if a != 0 && b > u64::MAX / a {
        u64::MAX
    } else {
        a * b
    }
}

/// con-leche: ConLeche/Frontend/Pace.lean:38-48 Pace.due
/// **Is a line due at item `k` of `total`**, counted from 1: the `.every` and
/// `.percent` arms; `false` at `.off` and at `.seconds`, whose clock arm is the
/// driver's (module note).
pub fn pace_due_count(p: &Pace, k: u64, total: u64) -> bool {
    match p {
        Pace::Off => false,
        Pace::Every(n) => *n > 0 && k % *n == 0,
        Pace::Percent(q) => {
            let d = sat_mul(*q, total);
            let km1 = if k > 0 { k - 1 } else { 0 };
            d > 0 && sat_mul(k, 100) / d != sat_mul(km1, 100) / d
        }
        Pace::Seconds(_) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_and_percent() {
        assert!(pace_due_count(&Pace::Every(3), 6, 10));
        assert!(!pace_due_count(&Pace::Every(3), 7, 10));
        assert!(!pace_due_count(&Pace::Every(0), 7, 10));
        // 5 % of 200 items: every tenth
        assert!(pace_due_count(&Pace::Percent(5), 10, 200));
        assert!(!pace_due_count(&Pace::Percent(5), 11, 200));
        assert!(!pace_due_count(&Pace::Seconds(1), 1, 1));
        assert!(pace_trace(&Pace::Every(1)));
        assert!(!pace_trace(&Pace::Every(2)));
        assert!(!pace_on(&Pace::Off));
    }
}

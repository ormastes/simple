//! `int.bits[lo..hi]` syntax sugar (B4 — bitfield slice).
//!
//! Desugars at parse time so that both the interpreter and HIR-lowering
//! paths see only plain bitwise / shift expressions — no new AST or HIR
//! variant required.
//!
//! Read form  : `x.bits[lo..hi]`        →  `(x >> lo) & mask`
//! Write form : `x.bits[lo..hi] = v`    →  `x = (x & ~mask) | ((v & mask) << lo)`
//!
//! `mask` is `(1 << (hi - lo)) - 1` and is built either as a constant fold
//! (when `lo` and `hi` are integer literals) or as a runtime expression
//! using shift/sub on integer literals so the field width can be dynamic.
//!
//! The receiver must be syntactically `x.bits[lo..hi]`. If the receiver of
//! `Slice` is a `FieldAccess` whose field name is anything other than
//! `bits`, the rewrite does nothing — normal Slice lowering is used.

use crate::ast::{BinOp, Expr, RangeBound, UnaryOp};

/// If `expr` is `x.bits[lo..hi]`, rewrite it into a mask+shift read
/// expression. Otherwise return `expr` unchanged.
///
/// In the AST, `x.bits[lo..hi]` parses as
///     `Index { receiver: FieldAccess { receiver: x, field: "bits" },
///              index: Range { start: Some(lo), end: Some(hi), bound: Exclusive } }`
/// because `0..8` is a `Range` expression and `[…]` is `Index`, not the
/// Python-style `Slice` (which uses `:`).
///
/// Inclusive-bound (`..=`) ranges are accepted and treated as `lo..hi+1` so
/// `bits[0..=7]` and `bits[0..8]` agree.
pub fn maybe_rewrite_bits_read(expr: Expr) -> Expr {
    if let Some((lvalue, lo, hi)) = try_match_bits_index(&expr) {
        return build_bits_read(lvalue, lo, hi);
    }
    expr
}

/// If `target` is a `.bits[lo..hi]` index on an L-value `x`, return
/// `Some((x, lo, hi_exclusive))` so the caller can synthesise the write
/// rewrite. Otherwise return `None`.
pub fn match_bits_write_target(target: &Expr) -> Option<(Expr, Expr, Expr)> {
    try_match_bits_index(target)
}

/// Shared matcher for both read and write sides.
///
/// Returns `(receiver_lvalue, lo_inclusive, hi_exclusive)` or `None`.
fn try_match_bits_index(expr: &Expr) -> Option<(Expr, Expr, Expr)> {
    let Expr::Index { receiver, index } = expr else {
        return None;
    };
    let Expr::FieldAccess { receiver: inner, field } = receiver.as_ref() else {
        return None;
    };
    if field != "bits" {
        return None;
    }
    let Expr::Range { start, end, bound } = index.as_ref() else {
        return None;
    };
    let lo = (**start.as_ref()?).clone();
    let raw_hi = (**end.as_ref()?).clone();
    // Normalise `..=hi` into `..hi + 1` so the field width is `hi - lo`.
    let hi_excl = match bound {
        RangeBound::Exclusive => raw_hi,
        RangeBound::Inclusive => Expr::Binary {
            op: BinOp::Add,
            left: Box::new(raw_hi),
            right: Box::new(Expr::Integer(1)),
        },
    };
    Some(((**inner).clone(), lo, hi_excl))
}

/// Build the value expression for `x.bits[lo..hi] = v`:
///     `(x & ~mask_at_lo) | ((v & mask) << lo)`
/// where `mask = (1 << (hi - lo)) - 1` and `mask_at_lo = mask << lo`.
///
/// Note: `target_lvalue` is duplicated into the value expression and so is
/// evaluated twice. Indices like `arr[i]` are pure in practice for the
/// crypto contexts that motivate B4. A side-effecting index expression
/// (e.g., `arr[next()]`) would observe the side effect twice; if that ever
/// becomes a concern, materialise the lvalue into a temp before rewriting.
pub fn build_bits_write_value(target_lvalue: Expr, lo: Expr, hi: Expr, value: Expr) -> Expr {
    let width = sub(hi, lo.clone());
    let mask = sub(shl(int_lit(1), width), int_lit(1));
    // Cache the field-shifted mask once (reused for both clear and set).
    // We don't introduce a temp — the shapes are simple enough that emitting
    // them twice is acceptable (HIR/MIR will fold equal subexpressions).
    let mask_at_lo = shl(mask.clone(), lo.clone());
    let cleared = bit_and(target_lvalue, bit_not(mask_at_lo));
    let masked_value = bit_and(value, mask);
    let shifted_value = shl(masked_value, lo);
    bit_or(cleared, shifted_value)
}

// ---- internal builders ------------------------------------------------------

fn build_bits_read(x: Expr, lo: Expr, hi: Expr) -> Expr {
    let width = sub(hi, lo.clone());
    let mask = sub(shl(int_lit(1), width), int_lit(1));
    let shifted = shr(x, lo);
    bit_and(shifted, mask)
}

fn int_lit(n: i64) -> Expr {
    Expr::Integer(n)
}

fn bin(op: BinOp, l: Expr, r: Expr) -> Expr {
    Expr::Binary {
        op,
        left: Box::new(l),
        right: Box::new(r),
    }
}

fn shl(l: Expr, r: Expr) -> Expr {
    bin(BinOp::ShiftLeft, l, r)
}
fn shr(l: Expr, r: Expr) -> Expr {
    bin(BinOp::ShiftRight, l, r)
}
fn bit_and(l: Expr, r: Expr) -> Expr {
    bin(BinOp::BitAnd, l, r)
}
fn bit_or(l: Expr, r: Expr) -> Expr {
    bin(BinOp::BitOr, l, r)
}
fn sub(l: Expr, r: Expr) -> Expr {
    bin(BinOp::Sub, l, r)
}
fn bit_not(e: Expr) -> Expr {
    Expr::Unary {
        op: UnaryOp::BitNot,
        operand: Box::new(e),
    }
}

//! Level-gated dispatch profiler for the AST interpreter (Phase D, startup perf plan).
//!
//! Default OFF. Enable with `SIMPLE_INTERP_PROFILE=1`; a histogram of `Expr`
//! variants seen by `evaluate_expr` is written to stderr (or to
//! `SIMPLE_INTERP_PROFILE_OUT`) at process exit via `libc::atexit`.
//!
//! When disabled the whole path is a single relaxed atomic load + branch, which
//! is why the counters can live behind a plain `Mutex` without affecting the
//! measured numbers.

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicU64, AtomicU8, Ordering};
use std::sync::Mutex;

use simple_parser::ast::Expr;

const UNKNOWN: u8 = 0;
const OFF: u8 = 1;
const ON: u8 = 2;

static STATE: AtomicU8 = AtomicU8::new(UNKNOWN);
static COUNTS: Mutex<Option<BTreeMap<&'static str, u64>>> = Mutex::new(None);

/// Identifier-read resolution outcomes, for judging inline-cache profitability.
pub static IDENT_READS: AtomicU64 = AtomicU64::new(0);
/// Inline-cache hits on the identifier fast path.
pub static IC_HITS: AtomicU64 = AtomicU64::new(0);
/// Inline-cache misses (cold, or invalidated by a generation bump).
pub static IC_MISSES: AtomicU64 = AtomicU64::new(0);

#[inline(always)]
pub fn enabled() -> bool {
    match STATE.load(Ordering::Relaxed) {
        OFF => false,
        ON => true,
        _ => init(),
    }
}

#[cold]
fn init() -> bool {
    let on = std::env::var("SIMPLE_INTERP_PROFILE")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(false);
    if on {
        *COUNTS.lock().unwrap() = Some(BTreeMap::new());
        // `libc` is a [target.'cfg(unix)'.dependencies] entry, so the at-exit
        // hook has to be cfg-gated for the crate to build on Windows. Say so
        // out loud instead of collecting counts that would never be printed --
        // this path only runs when SIMPLE_INTERP_PROFILE was explicitly set,
        // and a profiler that silently produces nothing is worse than one that
        // reports it is unavailable.
        #[cfg(unix)]
        unsafe {
            libc::atexit(dump_at_exit);
        }
        #[cfg(not(unix))]
        eprintln!(
            "[simple] SIMPLE_INTERP_PROFILE ignored: the at-exit dispatch dump is not wired on this platform"
        );
    }
    STATE.store(if on { ON } else { OFF }, Ordering::Relaxed);
    on
}

/// Record one dispatch of `expr`. No-op unless profiling is enabled.
#[inline(always)]
pub fn record(expr: &Expr) {
    if !enabled() {
        return;
    }
    record_kind(expr_kind(expr));
}

#[inline(never)]
fn record_kind(kind: &'static str) {
    if let Ok(mut g) = COUNTS.lock() {
        if let Some(map) = g.as_mut() {
            *map.entry(kind).or_insert(0) += 1;
        }
    }
}

extern "C" fn dump_at_exit() {
    let text = render();
    match std::env::var("SIMPLE_INTERP_PROFILE_OUT") {
        Ok(path) if !path.is_empty() => {
            let _ = std::fs::write(path, text);
        }
        _ => eprintln!("{}", text),
    }
}

/// Render the histogram, most frequent first. Public so specs can assert on it.
pub fn render() -> String {
    let g = COUNTS.lock().unwrap();
    let map = match g.as_ref() {
        Some(m) => m.clone(),
        None => BTreeMap::new(),
    };
    drop(g);
    let mut rows: Vec<(&'static str, u64)> = map.into_iter().collect();
    rows.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(b.0)));
    let total: u64 = rows.iter().map(|r| r.1).sum();
    let mut out = String::from("interp-dispatch-profile:\n");
    out.push_str(&format!("  total_dispatches: {}\n", total));
    for (k, v) in &rows {
        let pct = if total == 0 {
            0.0
        } else {
            (*v as f64) * 100.0 / (total as f64)
        };
        out.push_str(&format!("  {:<20} {:>12}  {:>6.2}%\n", k, v, pct));
    }
    out.push_str(&format!(
        "  ident_reads: {}  ic_hits: {}  ic_misses: {}\n",
        IDENT_READS.load(Ordering::Relaxed),
        IC_HITS.load(Ordering::Relaxed),
        IC_MISSES.load(Ordering::Relaxed)
    ));
    out
}

pub(crate) fn expr_kind(expr: &Expr) -> &'static str {
    match expr {
        Expr::Identifier(_) => "Identifier",
        Expr::Integer(_) | Expr::TypedInteger(_, _) => "Integer",
        Expr::Float(_) | Expr::TypedFloat(_, _) => "Float",
        Expr::Bool(_) => "Bool",
        Expr::Nil => "Nil",
        Expr::String(_) | Expr::TypedString(_, _) => "String",
        Expr::FString { .. } => "FString",
        Expr::Symbol(_) => "Symbol",
        Expr::BlockExpr { .. } => "BlockExpr",
        Expr::Binary { .. } => "Binary",
        Expr::Unary { .. } => "Unary",
        Expr::New { .. } => "New",
        Expr::Cast { .. } => "Cast",
        Expr::Lambda { .. } => "Lambda",
        Expr::If { .. } => "If",
        Expr::Match { .. } => "Match",
        Expr::DoBlock(_) => "DoBlock",
        Expr::UnsafeBlock(_) => "UnsafeBlock",
        Expr::Call { .. } => "Call",
        Expr::MethodCall { .. } => "MethodCall",
        Expr::FieldAccess { .. } => "FieldAccess",
        Expr::Array(_) | Expr::VecLiteral(_) => "Array",
        Expr::ArrayRepeat { .. } => "ArrayRepeat",
        Expr::Tuple(_) | Expr::LabeledTuple(_) => "Tuple",
        Expr::Dict(_) => "Dict",
        Expr::Range { .. } => "Range",
        Expr::Index { .. } => "Index",
        Expr::TupleIndex { .. } => "TupleIndex",
        Expr::Path(_) => "Path",
        Expr::StructInit { .. } => "StructInit",
        Expr::ListComprehension { .. } => "ListComprehension",
        Expr::DictComprehension { .. } => "DictComprehension",
        Expr::Slice { .. } => "Slice",
        Expr::Spread(_) | Expr::DictSpread(_) => "Spread",
        Expr::MacroInvocation { .. } => "MacroInvocation",
        Expr::Await(_) => "Await",
        Expr::Spawn(_) => "Spawn",
        Expr::Yield(_) => "Yield",
        _ => "Other",
    }
}

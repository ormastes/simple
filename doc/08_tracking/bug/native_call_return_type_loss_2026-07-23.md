# native (bootstrap): declared function return types ignored — call results all typed i64

- **Date:** 2026-07-23  **Status:** PARTIALLY FIXED (Str returns; other types
  remain on the builtin-table fallback by design, see ceiling)
- **Severity:** critical — every text-returning call rendered as raw integers
  in interpolation/concat (LSP server responses built as digit soup /
  silently empty; W86 `jp` produced "2099601name2099601:v1").

## Root cause (probe chain W87→W91)
`hir_lowering/_Items/declaration_lowering.spl` `lower_function`: in
SIMPLE_BOOTSTRAP mode the return type came ONLY from
`bootstrap_builtin_return_type(name)` (small name table, i64 default) —
the DECLARED `-> text` was ignored. This was a workaround from when the
flat-AST bridge discarded declared return types entirely
(convert_nodes.spl `inferred_ret` comment); after the bridge was fixed, the
workaround inverted into a silent re-typing of every function.

Downstream: call dests typed i64 → `local_is_str` false →
`coerce_concat_operand`/interpolation route through rt_raw_i64_to_string →
pointer digits. `.len()` still worked (runtime tag dispatch), which made the
symptom look "context-sensitive".

## Fix (landed with this doc)
Declared type takes priority — NARROWED in bootstrap mode to Str returns
only. Plus a cross-module name→MirType registry
(mir_data.bootstrap_fn_ret_type_*) populated by the three bootstrap prep
loops and consulted by bootstrap_resolved_call_return_type when the symbol
lookup fails (HIR symbol mutations do not survive the pass boundary).

## Ceiling / follow-up
Widening ALL declared types immediately broke i64-convention consumers:
`get_args() -> [text]` became an Array-typed local and `a.len()` lowered to
the raw receiver (no len call) → strlen SIGSEGV (W92). Widen per type-kind
with repro coverage: Array, Dict, struct/class Named, f64, Optional.

## Repro
W87: `fn t1() -> text: "xy"` + `print "{t1()}"` → printed `2099630`
(pointer digits). Fixed: prints `xy` (W91/W93).

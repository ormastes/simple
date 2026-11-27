# Seed interpreter has no dispatch entry for spl_ordered_key_cmp / spl_collection_capture_*

Status: open (diagnosed, not fixed; fix needs a seed rebuild, banned in this lane)
Class: (c) seed/interpreter defect. Found by lane `xraychk` on Windows, seed-tip, 2026-11-14.

## Repro
`simple test test/01_unit/lib/collections/adaptive_set_filter_spec.spl` -> 0/7
(`semantic: unknown extern function: spl_collection_capture_note_size`),
`adaptive_set_loop_spec.spl` -> 0/10, `adaptive_policy_adapter_spec.spl` -> 11/13
(`unknown extern function: spl_ordered_key_cmp`). Same on Linux aarch64 (earlier evidence).

## Exact gap
- Declared in Simple: `src/lib/nogc_sync_mut/sffi/ordered_key_cmp.spl`,
  `src/lib/nogc_sync_mut/sffi/collection_capture.spl`.
- Backed natively: `src/runtime/runtime_native.c` (C) and the Rust runtime
  `src/compiler_rust/runtime/src/value/sffi/ordered_key.rs`, `capture_text.rs`,
  symbols in `common/src/runtime_symbols.rs`, `codegen/runtime_sffi.rs`.
- NOT registered in the interpreter table
  `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` (`init_dispatch_table`),
  so any spec on the seed interpreter that reaches a capture-aware or ordered-map path fails.
- A pure-Simple fallback is NOT acceptable: the extern is the single ABI owner (erased-key
  order must match the native comparator, capture engine is process-global).

## Fix
Add `insert_simple!` entries bridging to the existing Rust owners in `interpreter_extern`, rebuild the seed,
re-run the three specs. `Dict.capacity` (named in the status doc) did not reproduce in any run here.

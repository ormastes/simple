# Seed interpreter: `text.from_bytes(b)` fails with "variable `text` not found"

- **Status:** FIXED 2026-11-06 (branch `work/seed-interp-batch2-20261106`)
- **Found:** 2026-11-06 by the seed JIT lane (compiled lanes route it to `rt_bytes_to_text`).
- **Engine:** Rust seed tree-walk interpreter.

## Symptom

```
val b: [u8] = [97u8, 98u8, 99u8]
print(text.from_bytes(b))
```

`SIMPLE_EXECUTION_MODE=interpret`: `error: semantic: variable `text` not found`.
Used in product code, e.g. `src/lib/nogc_sync_mut/mcp/dispatch.spl` `_bytes_text`.

## Root cause

The interpreter special-cases the builtin `text` statics in
`interpreter_method/mod.rs` (`evaluate_method_call` and
`evaluate_method_call_with_self_update`), but only `text.from_char_code`;
`from_bytes` fell through to evaluating `text` as a variable. LLVM codegen
(`codegen/llvm/functions/calls.rs`) and the pure-Simple backend route
`text.from_bytes` to `rt_bytes_to_text`.

## Resolution

Both interpreter sites now answer `text.from_bytes(b)` through the
interpreter's `rt_bytes_to_text` extern (`interpreter_extern/conversion.rs`,
byte-preserving since `seed_rt_bytes_to_text_lossy_utf8_split_scalar_2026-10-31`).

Evidence: `test/fixtures/seed_interp/text_from_bytes_static_repro.spl`,
interpreter mode. Before: ``error: semantic: variable `text` not found``.
After: `text_from_bytes abc`. Rust test
`interpreter_method::text_from_bytes_static_tests::text_from_bytes_builds_text_from_a_byte_array`:
FAILED before (``variable `text` not found``), ok after.
(The debug-build seed JIT overflowed its stack on this file on this host;
not investigated here.)

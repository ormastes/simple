# Seed interpreter: an aliased import of an `extern fn` is "function not found"

- Status: OPEN
- Date: 2026-10-19
- Lane: Rust seed tree-walk interpreter (`bin/simple test` on the seed)
- Impact: SOSIX cannot expose a runtime extern as a zero-cost `export use
  ... as` rename; `std.nogc_sync_mut.sosix.secure_temp_dir` uses thin
  `@always_inline` facades instead until this is fixed.

## Repro

```
# src/lib/nogc_sync_mut/sosix/zz_probe_rt.spl
extern fn rt_file_mode(path: text) -> i64
# spec
use std.nogc_sync_mut.sosix.zz_probe_rt.{rt_file_mode as one_hop_mode}
... one_hop_mode("/tmp")   # semantic: function `one_hop_mode` not found
```

Same for a two-hop `export use m.{rt_x as sosix_x}` re-export. Without the
alias the call works. Native lanes are fine: the seed's codegen and the
pure-Simple compiler (Stage 2 binary building a probe) both resolve the alias
to the `rt_` symbol with the (ptr, len) text split.

## Cause

Extern declarations are registered only by name in the global
`EXTERN_FUNCTIONS` set (`module_evaluator/evaluation_helpers.rs`, `Node::Extern`);
they are never module exports, so the `ImportTarget::Aliased` arms
(`interpreter_eval.rs`, `evaluation_helpers.rs` import/export, `node_exec.rs`,
`block_execution.rs`) find nothing under `name` and bind nothing under `alias`.

## Fix sketch

At those Aliased arms, when `name` is an extern the loaded module itself
declared (not merely a coincidental runtime-manifest symbol), record
`alias -> name` in a thread-local map, add `alias` to `EXTERN_FUNCTIONS`, and
resolve the map at the top of `call_extern_function_with_values`; clear it with
the other interpreter state.

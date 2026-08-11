---
name: Interpreter Performance Bottlenecks
description: Top 5 interpreter perf bottlenecks identified 2026-05-11 — all require Rust-layer changes
type: reference
---

Top 5 interpreter performance bottlenecks (researched 2026-05-11):

1. **Per-statement Mutex lock in `debug_state()`** — `exec_node()` calls `DEBUG_STATE.lock()` on every statement before checking `ds.active`. Fix: guard with `AtomicBool`. Path: `compiler/src/interpreter/node_exec.rs:46-58`

2. **`Value::Str(String)` not Arc-wrapped** — deep-copies bytes on every clone (fn call, capture, env freeze). Fix: `Str(Arc<str>)`. Path: `compiler/src/value.rs`

3. **975-arm string match for extern dispatch** — `call_extern_function()` matches `name` against ~975 arms. Fix: static `HashMap<&'static str, fn(...)>` or `phf`. Path: `compiler/src/interpreter_extern/mod.rs`

4. **5-stage expression cascade** — `evaluate_expr` calls 5 sub-dispatchers sequentially, each matching the same discriminant. Fix: fuse into single match. Path: `compiler/src/interpreter/expr.rs:182-220`

5. **Per-statement coverage/location overhead** — `record_node_coverage()` + `extract_node_location()` on every statement even when unused.

Quick win: guard `debug_state` with `AtomicBool` + hoist `extract_node_location` inside the `ds.active` branch.

All require Rust changes in `src/compiler_rust/compiler/`.

# Seed: `f(obj.field)` write-back copy-on-writes the object's field map against a DEAD alias

- **Date:** 2026-08-23
- **Component:** Rust seed, AST interpreter — argument write-back
- **Class:** COW clone that fires when no live alias exists
- **Status:** FIXED

## Symptom

Every call of the shape `f(obj.field)` — a plain function taking one of an
object's container-valued fields — deep-copied the caller object's whole
`HashMap<String, Value>` field map. Not sometimes: *every* time, unconditionally,
independent of whether anything else held the object.

Measured on a 200-call loop with the new counters:

| | `FIELD_WRITEBACK_CALLS` | `FIELD_WRITEBACK_MAP_CLONES` |
|---|---|---|
| pre-fix | 200 | **200** |
| post-fix | 200 | **0** |

## Mechanism

`interpreter_call/core/function_exec.rs`, `ArgSource::Field` write-back:

```rust
if let Some(obj_val) = outer_env.get(&obj_name).cloned() {
    if let Value::Object { class, mut fields } = obj_val {
        Arc::make_mut(&mut fields).insert(field_name, callee_val);
        outer_env.insert(obj_name, Value::Object { class, fields });
```

`.cloned()` produces a SECOND handle while `outer_env` keeps the first, so
`Arc::strong_count(&fields) >= 2` and `Arc::make_mut` is *guaranteed* to clone.
The alias it protects is dead: the binding is overwritten two lines later, and
the frame is suspended in the middle of a return sequence, so nothing can
observe the intermediate state.

This is a bug, not tuning: the copy encodes no information and protects no
observer. Value semantics are untouched — a *live* alias (the object also
reachable from a shared base/scope layer) still gets copy-on-write.

## Fix

Two new `CowEnv` primitives (`value.rs`):

- `take_frame_owned(key)` — removes `key` from THIS frame's overlay, but only
  when the frame is its sole home (no shared base/scope binding, no pending
  tombstone). Returns `None` and leaves the env byte-identical whenever removal
  would be observable, so the shared-layer case keeps the old copy-on-write.
- `restore_frame_owned(key, value)` — puts a taken value back *without*
  recording a frame write, for the paths that decide not to write. Preserves the
  dirty-only block/closure write-back landed in `af095a88ffd`.

The write-back now takes the handle out before mutating and falls back to the
old `get().cloned()` path when the frame does not own it outright.

## Class sweep (standing rule 1)

Three sites had the identical mechanism; all three are fixed in this change:

1. `function_exec.rs` `ArgSource::Field` — object field map (above).
2. `function_exec.rs` `ArgSource::Identifier`, value-type-struct branch —
   `outer_env.get(&caller_name).cloned()` feeding
   `merge_shared_collection_fields`, whose `Arc::make_mut` copies the struct's
   field map for the same dead-alias reason.
3. `interpreter_call/core/lambda.rs` `Expr::FieldAccess` — the lambda twin of
   site 1, byte-for-byte the same shape.

Ratchet: `scripts/check/check-perf-regression-tests.shs` pins `take_frame_owned`
at all three sites plus the `clones == 0` counter assertion, so a re-introduced
`get().cloned()` at any of them fails the gate.

## Twin check (standing rule 2)

- **Pure Simple compiler:** the pure-Simple interpreter does not have this
  write-back shape (argument write-back is expressed through the Simple-level
  env API, which has no `Arc::make_mut`). No twin. The sibling lane at
  `/mnt/fast/wt-splperf-1` owns that side.
- **C-runtime dict tombstone/load-factor bug (`e24b2845b3b`) — checked, NO twin
  in the Rust runtime.** `runtime/src/value/dict.rs` `rt_dict_remove` uses
  *backward-shift* deletion (it rehashes the rest of the probe chain into the
  hole) and decrements `len`; there are no tombstones anywhere in the file, so
  the 3/4 grow test at `dict.rs:258` measures live entries, not churn. Recorded
  here so the negative is not re-investigated.

## Evidence

- `src/compiler_rust/compiler/tests/interpreter_field_writeback_no_dead_alias_copy.rs`
  — FAILS pre-fix (`field map copied 200 times across 200 write-backs`),
  passes post-fix. Second test asserts the callee's mutation is still published
  and the object's other fields survive.
- Real workload (`bin/simple run src/app/cli/bootstrap_main.spl compile
  src/compiler/20.hir/hir_lowering/module_surface_registry.spl`, identical
  command both sides): peak RSS **2,352,152 KB → 2,308,256 KB** (-43 MB),
  wall 2:16 → 2:05. This workload is dominated by module loading rather than
  field write-back, so the counter pin, not the RSS delta, is the mechanism
  evidence.

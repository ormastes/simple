# Lane PMR — Rust seed interpreter place model

Status: **DONE — oracle GREEN, regression A/B clean.** Not committed (coordinator lands).

## Defect

The Rust seed interpreter had no place/lvalue model. Field assignment was
hand-written for exactly two levels and rejected anything deeper with
`"invalid assignment: deeply nested field access requires intermediate
variables"`. The mutating-method **receiver** path had the same two-level
ceiling but **no guard**, so `a.b.c.mutate()` evaluated the receiver to a copy,
mutated the copy, and dropped the write silently. Loud on assignment, silent on
the method spelling of the identical operation.

## Fix

New module `src/compiler_rust/compiler/src/interpreter/place.rs`.

A place = environment-rooted variable + arbitrary chain of field/index
projections. Because interpreter values are `Arc`-based copy-on-write
(`Value::Object { fields: Arc<HashMap<..>> }`, `Value::Array(Arc<Vec<..>>)`),
the model is a projection **path** plus `Arc::make_mut` descent, not a held
`&mut` chain — this sidesteps the borrow checker and preserves COW semantics
exactly (unique containers mutate in place, aliased ones deep-copy first).
Arrays remain value types; no aliasing is introduced.

API:
- `resolve_place(expr, ..) -> Option<Place>` — `None` for non-places
  (temporaries, call results), so those keep today's copy behavior.
  Index expressions are evaluated once, here.
- `write_place(env, place, value) -> bool` — parent-navigate then insert at the
  last projection (so assigning a not-yet-existing field creates it, matching
  the existing `HashMap::insert` behavior). `false` = "not a live place",
  callers fall back rather than erroring.
- `updated_root(env, place, value)` — same write, returned as a fresh ROOT value
  for call sites that hand a `(variable, new_value)` update to their caller.
- `place_is_live(env, place)` — read-only liveness probe (must not promote the
  root out of the shared env base just to answer a question).

Wired into **four** call sites (the receiver path is reachable from three
distinct dispatchers, which is why the original 2-level ceiling was duplicated):

| File | Site |
|---|---|
| `interpreter/node_exec.rs` | the two `exec_assignment` error branches — deep field assignment now resolves a place; error text only remains for genuine non-places |
| `interpreter_helpers/patterns.rs` | `handle_method_call_with_self_update` — **statement-position** method calls (the path the failing spec actually used) |
| `interpreter/expr/calls.rs` | `eval_call_expr` MethodCall arm — expression-position, 3 fall-through sites |

Existing 1- and 2-level fast paths are untouched; the place model is a
fall-through, so the change is additive and low-blast-radius.

## Build

```bash
cd src/compiler_rust && cargo build --release -p simple-driver --bin simple
# artifact: src/compiler_rust/target/release/simple  (this IS the Rust seed;
# bin/simple is a symlink to bin/release/<triple>/simple, also the seed)
cargo test --release -p simple-compiler --lib interpreter   # 474 passed, 0 failed
```

## Verification

Oracle `test/01_unit/compiler/two_hop_field_method_mutation_spec.spl`
(spec + fixture UNTOUCHED):

| binary | verdict |
|---|---|
| pre-change (built from same source, same profile) | 5 examples, **4 failures** |
| post-change | 5 examples, **0 failures** |

Regression sweep, every `"N examples, M failures"` line, fixed vs true baseline
binary — **identical on every spec except the oracle**:

| spec | base | fixed |
|---|---|---|
| os/services/tty_termios_ld | 5/0 2/0 2/0 4/0 3/0 | same |
| os/services/container/container_manager | 4/0 | same |
| os/services/ds_service | 2/0 3/0 2/0 2/0 2/0 2/0 4/0 | same |
| os/arch/duplicate_owner | 4/0 2/0 | same |
| compiler/interp_object_store_ref_model | 3/0 | same |
| compiler/interpreter_system_spec_body_probe | 4/0 | same |
| compiler/struct_init_field_order_fill | 4/**2** 3/0 | 4/**2** 3/0 — **pre-existing red, A/B proven** |
| compiler/global_var_type | 5/0 | same |
| compiler/default_param_call_fill | 6/0 | same |
| compiler/empty_array_map_lambda | 2/0 | same |
| compiler/bdd_truthy_runtime | 4/0 | same |
| compiler/two_hop_field_method_mutation | 5/**4** | 5/**0** |

`struct_init_field_order_fill` fails on omitted-struct-field zero-fill in BOTH
binaries — unrelated to place resolution, not caused here.

The `src/os/**` extract-mutate-write-back workarounds remain correct: all four
mandated OS specs stay 0-failure, and oracle example 5 pins the direct chain and
the manual workaround to the same answer.

## ENVIRONMENT LANDMINE (cost ~2h, affects every lane)

`simple test` routes specs through a **persistent session daemon**, and the
daemon on this machine was running a **stale `src/compiler_rust/target/debug/simple`**
(a debug-profile build from an earlier session). Every `simple test` verdict was
therefore produced by that stale binary — a freshly built, freshly deployed
`bin/simple` changed **nothing**, and the oracle stayed red at exactly 5/4 while
the same spec run directly was green.

Symptom to recognise: the fix demonstrably works via
`SIMPLE_EXECUTION_MODE=interpret bin/simple run <spec>` but `bin/simple test
<spec>` is byte-identically red, and `--no-cache` does not change it.

Workaround used for every verdict above: **`--no-session-daemon`**. Diagnosis
route that worked: poll `ps -eo pid,args` for children during the run — the
daemon shows up as `target/debug/simple run src/app/test_daemon/light_daemon.spl`.
Note `SIMPLE_PLACE_DEBUG`-style `eprintln!` probes are useless here (the runner
captures child stderr); probe on **stdout** instead.

## Clobber note

Mid-lane, a parallel session's sync wiped this lane's uncommitted working-copy
changes (git status went clean, `place.rs` deleted). Restored from out-of-tree
backups after verifying with `diff <(git show HEAD:<path>) <backup>` that every
HEAD-only line was exactly a line these edits intentionally replaced — zero
upstream work reverted. Re-built and re-verified on the new HEAD (oracle 5/0).

## Deliberately left alone

- `src/compiler/**` (pure-Simple interpreter — lane PMS), `src/lib/.../ecs/**`
  (lane ECSME), `src/os/**`, and the oracle spec/fixture.
- `bin/release/<triple>/simple` was restored to its original bytes; deploying is
  outside this lane's owned paths.
- Composite dict keys (`Value::wrap_dict_entry` marker tuples) are not modelled
  as places — only scalar-keyed dict entries. Non-scalar keys fall back.
- The existing 1-/2-level fast paths were not collapsed into the place model.
  They are correct and heavily exercised; unifying them is a follow-up, not a
  prerequisite.

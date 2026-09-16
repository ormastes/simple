# Interpreter: `me` method receiver stays aliased for the whole body, making every `self.<container>` write an O(n) COW clone — 2026-08-21

## Status
FIXED 2026-08-21 (seed, Rust interpreter). Commit: see below.

## Symptom
Stage-1 bootstrap (self-hosted `src/compiler` interpreted by the Rust seed):
HIR import registration cost 1.7 -> 15.8 ms per `register_imported_symbol`
call and grew with the accumulated closure; the per-module HIR phase was
~100x slower than the same algorithm under the JIT.

Isolated (`/mnt/data/seedperf/mut_isolate.spl`, `SIMPLE_EXECUTION_MODE=interpreter`,
deployed seed, shared box load ~30):

| shape (`me` method on a class, n calls) | n=1500 | n=3000 | n=6000 |
|---|---|---|---|
| `self.ints.push(i)` | 110 ms | 225 ms | 758 ms |
| `self.names.push("n{i}")` | 105 ms | 264 ms | 1137 ms |
| `self.surfaces.push(Struct(..))` | 297 ms | 658 ms | 3107 ms |
| `self.index_by_name["n{i}"] = i` | 207 ms | 616 ms | 3322 ms |
| local `arr.push(i)` (control) | 4 ms | 10 ms | 19 ms |
| local `d["n{i}"] = i` (control) | 4 ms | 11 ms | 23 ms |

4x the count costs 7-16x the time: quadratic. The same shapes under the JIT
take 15 ms for the whole 3000-entry registry build.

## Mechanism
`interpreter_helpers/patterns.rs` (`handle_method_call_with_self_update_inner`,
identifier receiver): the "zero-copy" path `env.remove(obj_name)` takes the
receiver's `Arc<HashMap>` out of the env so the body owns it uniquely — and
the very next statement re-inserts a clone of it (the 2026-06-11 fix so that
an argument like `me.field` can still resolve during `bind_args`). That clone
is never removed, so `self`'s field map has `strong_count == 2` for the ENTIRE
method body. Every `self.xs.push(v)` / `self.d[k] = v` then takes the aliased
branch of `Arc::make_mut`: clone the field `HashMap`, then deep-clone the
`Vec`/`HashMap` container. gdb stack samples of the push loop land in
`Arc::make_mut -> Vec::clone -> Value::clone` under
`try_field_array_mutation_in_place`, plus `RawTable::drop` for the discarded
map — per call.

Two further paths had the same aliasing:
- field receiver `o.inner.m()` (statement position) cloned the PARENT object
  out of the env and called `find_and_exec_method_with_self(&field_fields)`,
  pinning both maps (this is `self.symbols.define(..)` in HIR lowering — the
  whole symbol table was copied per define, which is exactly a cost that grows
  with the closure);
- expression position (`val r = o.m()`, `interpreter_method/mod.rs`)
  evaluated the receiver to a clone and borrowed the Arc for the body.

## Fix
`interpreter_method/special/execution.rs`: `SelfAlias { root, field }` with
`release` (drop the caller's alias right after `bind_args`, before the body)
and `restore` (put the binding back on every exit, Ok or Err, O(1) Arc bump).
`exec_function_with_self_return_releasing` takes the optional alias; the
existing entry points are unchanged wrappers. The three call sites above pass
the alias. For the nested-field case the entry is only removed when the parent
map is itself uniquely owned (`Arc::get_mut`); otherwise nothing changes.

Semantics preserved: the alias is dead weight by construction — the caller
always overwrites it with `updated_self` — so releasing it cannot change any
observable value. A binding genuinely aliased by ANOTHER live name still has
`strong_count > 1` and still copies on write (pinned by test).

## Measurement (after)
Same programs, seed built from the same tree at origin/main `096e9adbc4f`
before/after this change (`/mnt/data/seedperf/simple.{baseline,fixed}`),
`SIMPLE_EXECUTION_MODE=interpreter`, shared box load ~30 (envelope, not A/B
on an idle machine):

| shape | baseline n=3000 | fixed n=3000 | baseline n=6000 | fixed n=6000 |
|---|---|---|---|---|
| `self.ints.push(i)` | 158 ms | 28 ms | 455 ms | 86 ms |
| `self.names.push("n{i}")` | 169 ms | 33 ms | 701 ms | 72 ms |
| `self.surfaces.push(Struct(..))` | 536 ms | 47 ms | 2715 ms | 111 ms |
| `self.index_by_name["n{i}"] = i` | 496 ms | 221 ms | 2737 ms | 79 ms |
| registry build, 3000 entries (4 writes per add) | 2895 ms | 534 ms | | |

Doubling n now doubles the time: linear. n=6000 struct push 2715 -> 111 ms
(24x), dict set 2737 -> 79 ms (35x). Real HIR specs in interpreter mode:
`hir_package_dependency_scan_memo_spec.spl` 22.7 s -> 16.1 s,
`hir_module_callable_index_spec.spl` 7.2 s -> 6.7 s, same verdicts.

The remaining gap to a local-variable write (28 ms vs 12 ms for 3000 pushes)
is plain per-call interpreter overhead (env setup, arg binding), not cloning.

## Not fixed here
- `fn f(self: S)` / by-value struct params and any receiver that is NOT a
  bound name or `name.field` (e.g. `a[i].m()`, `a.b.c.m()`) still go through
  copying paths.
- The tree-walk interpreter is still ~10 us per simple statement (e.g. the
  `ordered_names[i] == name` scan: 150k iterations = 950 ms either way); that
  is the inherent interpreter/JIT gap, not an aliasing defect.

## Pins
`src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` tests:
- `me_method_push_on_self_field_mutates_in_place` (identifier receiver, < 64
  distinct buffers for 2000 calls; pre-fix ~2000)
- `me_method_on_nested_field_object_mutates_in_place` (`o.inner.add(v)`)
- `me_method_in_expression_position_mutates_in_place` (`evaluate_expr` path)
- `me_method_receiver_genuinely_aliased_by_another_name_still_copies`
- `me_method_error_restores_receiver_binding`

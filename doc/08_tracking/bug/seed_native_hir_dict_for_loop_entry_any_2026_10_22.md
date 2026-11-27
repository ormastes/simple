# Seed native HIR: dict for-loop entry typed ANY hard-fails field access

## Observed failure

Stage 2 (`--full-bootstrap --stop-after-stage2`, seed native pipeline
`SIMPLE_NATIVE_BUILD_RUST=1`) on release_phase3 @ bfcc3125bc8 failed with
exactly one file:

```
src/compiler/35.semantics/safety_checker_places.spl:
hir: Unsupported feature: cannot infer field type while lowering
safety_alias_join: struct 'ANY' field 'owner_id'
```

1483 files compiled; this was the sole failure (`failed=1`).

## Root cause

`TypeRegistry::get_iterable_element`
(`src/compiler_rust/compiler/src/hir/type_registry.rs:214`) has cases for
Array/String/Tuple/LabeledTuple but **no Dict case**, so
`for entry in some_dict` binds the loop variable as `TypeId::ANY`
(`hir/lower/stmt_lowering.rs:1054-1078`, tuple destructuring at :1081-1134
propagates the same ANY into both pattern bindings). Any field access on the
entry (`entry[1].owner_id`) is then field-access-on-ANY and the native HIR
pass hard-fails (`hir/lower/expr/access.rs:466`). The interpreter tolerates
the same source, so the defect is native-only, matching the class documented
in `doc/08_tracking/bug/native_dict_items_missing_lowering_2026_10_18.md`
(direct pair loops derive field types in the pure-Simple MIR producer, but
the Rust seed's HIR pass does not).

## Workaround (applied 2026-10-22)

`safety_alias_join` re-reads both aliases by key
(`first[entry[0]]` / `second[entry[0]]` into `val ... : SafetyClassAlias`)
before touching fields: typed dict index reads carry the value type, so
`.owner_id` / `.roots` resolve. Raw `entry[0]` indexing of the ANY entry is
tolerated by the lowering. Marked with a bug-linked `@workaround` comment in
`src/compiler/35.semantics/safety_checker_places.spl`.

## Proper repair (not done)

Add a Dict case to `get_iterable_element` returning a `(K, V)` entry type.
Caution: runtime dict iteration yields 2-element arrays
(`rt_dict_entries`, see `runtime_bridge.rs:279`), so the static entry type
must match the runtime representation the For codegen consumes — a naive
`Tuple[K, V]` risks an ABI mismatch. Needs a dedicated lane with both
backend evidence.

## Update 2026-10-22

The equivalent key-iteration repair landed as 83548ce08dd (PR #4121,
"robust safety_alias_join inference") with a TypeId-shift framing. This doc
retains the precise mechanism: `get_iterable_element` has no Dict case, so
dict for-loop entries lower as ANY and native HIR hard-fails field access.
Proper repair (not done): type dict iteration entries, matching the runtime's
2-element-array entry representation — see the original "Proper repair" note.

## Update 2026-11-05 — FIXED (seed HIR lane)

`TypeRegistry::get_iterable_element` (compiler/src/hir/type_registry.rs) now
has a `HirType::Dict { key, value }` arm returning a registered
`HirType::Tuple([K, V])`. Entry representation chosen after checking all
three producers/consumers end to end:

- Runtime: `rt_for_iterable(dict)` -> `rt_dict_entries`
  (runtime/src/value/dict.rs) returns an ARRAY of `rt_tuple_new(2)` heap
  TUPLE handles — one tagged tuple word per entry.
- Interpreter: `get_iterator_values` (interpreter_call/block_execution.rs)
  binds `Value::Tuple([key, value])`.
- Pure-Simple MIR producer: dict entries lane (50.mir/mir_lowering_stmts.spl
  :4547-4571) types the entry `Tuple(K, V)` from the dict's key/value types.
- Seed codegen: every non-primitive TypeId incl. Tuple is ONE pointer-sized
  word (codegen/types_util.rs `type_id_to_cranelift`/`type_id_size`), so a
  Tuple-typed loop slot holds the tagged tuple handle verbatim — no
  aggregate-layout ABI mismatch (the bug doc's "2-element array" caution
  refers to the entries ARRAY, not the entry itself; the entry is a tuple
  handle, and Tuple is the correct static type for it).

`entry[i]` then lowers through the existing tuple paths (HIR access.rs
tuple-index typing; MIR `rt_tuple_get`), and tuple destructuring
`for (k, v) in dict` propagates K/V into both bindings.

### Evidence

1. TDD (CARGO_TARGET_DIR=/private/tmp/rel100-cargo-b, `-p simple-compiler
   --lib`): 3 new tests in hir/lower/tests/control_flow_tests.rs
   (`dict_for_loop_entry_is_typed_key_value_tuple`,
   `dict_for_loop_tuple_destructure_binds_key_and_value_types`,
   `dict_for_loop_entry_value_field_access_lowers`) — all failed pre-fix
   (entry lowered as ANY), all pass post-fix. Full `hir::` module: 463
   passed, 0 failed. Full compiler lib suite: 4521 passed, 24 failed — all
   24 verified pre-existing at branch baseline (linker/macOS-version and
   other lanes' in-progress failures), unrelated to this change.
2. Reproduced the exact original failure with the pre-fix seed binary
   (`simple native-build` on a standalone source with `for entry in dict` +
   `entry[1].owner_id` and a second `owner_id` struct at a different slot):
   `hir: Unsupported feature: cannot infer field type while lowering
   count_matches: struct 'ANY' field 'owner_id'`. With the fixed binary the
   same command compiles (1 compiled, 0 failed) and the produced native
   binary prints the correct result (`1 1 1`), covering both the scalar
   entry loop and the `for (k, v) in dict` destructure loop.
3. Regression guard on the original victim: `native-build --entry
   src/compiler/35.semantics/safety_checker_places.spl --entry-closure
   --source src/compositions/kernel_llvm_cranelift --source src` (env
   mirrors stage1/stage2: SIMPLE_BOOTSTRAP=1 SIMPLE_NO_STUB_FALLBACK=1
   SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_SCV_INVENTORY_COLD_INIT=1
   SIMPLE_PARSE_SHARDING=0): 125 compiled, 0 failed, with the fixed binary
   (same as pre-fix). Interpreter path: the same repro source runs
   correctly through the seed interpreter (`1 1 1`); the real file reaches
   the expected standalone-SMF interpreter-construct gate (36 functions
   using TryOperator/PatternMatch), unchanged behavior.

Note: the release/1.0.0 copy of safety_checker_places.spl already carries
the 2026-10-22 workaround (key-iteration + typed re-reads), so it no longer
exercises the failure; the standalone repro above restores the pre-workaround
form for verification.

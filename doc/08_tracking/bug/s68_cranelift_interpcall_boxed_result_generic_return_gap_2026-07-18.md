# Follow-up: seed cranelift InterpCall boxed-result gap for generic/composite return types

**Date:** 2026-07-18
**Lane:** S68
**Status:** Dict return case FIXED (S78, 2026-07-18) — see "Fix (S78)" below.
Enum/Option/Result FIXED (S82, 2026-07-18) — see "Fix (S82)" below. Object
has NO sound fix at this bridge layer; the silent NIL collapse was converted
to a LOUD failure (panic) instead — see "Fix (S82)" for the precise registry
gap.
**Severity:** P2 (silent wrong result), seed `--native --backend=cranelift` path only.

## Context

Lane S68 root-caused and fixed
`doc/08_tracking/bug/s59_cranelift_dict_return_abi_root_cause_2026-07-17.md`:
`Expr::Dict` literals unconditionally added `FallbackReason::CollectionLiteral`
in `compiler/src/compilability.rs`, forcing every *caller* of a Dict-returning
function through `MirInst::InterpCall` (the hybrid interpreter-bridge call).
That fix removed the Dict-literal-specific trigger — Dict literals now stay on
the native path exactly like the already-fixed Array/Tuple literals.

That fix does **not** close the underlying mechanism. It only removes one of
several possible reasons a function can be forced through `InterpCall`.

## The residual gap

`compile_interp_call` in `compiler/src/codegen/instr/core.rs` (~line 758-839)
decides how to convert the interpreter's boxed `RuntimeValue` result back to a
native value:

```rust
let is_extern_bridge = func_name.starts_with("rt_") || func_name.starts_with("spl_");
let keep_boxed_result = boxed_result || interp_call_keeps_boxed_result(func_name);
let value = if !keep_boxed_result && (... f64 ...) {
    call_runtime_1(ctx, builder, "rt_value_as_float", result)
} else if !keep_boxed_result && (is_extern_bridge || vreg_is_native_equality_scalar(ctx, *d)) {
    call_runtime_1(ctx, builder, "rt_value_raw_i64", result)
} else {
    result   // <-- stays as the interpreter's boxed RuntimeValue
};
```

For a **plain user-defined function** (not `rt_`/`spl_` prefixed) whose call
destination vreg has no recognized scalar type (the common case for
Dict/Array/struct/Option returns — comment in `compilability.rs::return_type_keeps_boxed`
confirms "Call dests carry no entry in vreg_types" for these), execution falls
to the final `else` branch: the interpreter's boxed `RuntimeValue` wrapper is
stored into the vreg **unconverted**. Downstream native consumers (e.g.
`Dict.len()`, `Dict.contains_key()`, native indexing) expect the runtime's
native tagged-pointer handle, not the interpreter's boxed wrapper, and read
garbage — this is exactly the S59/S68 symptom (`len()` = -1, etc.).

`return_type_keeps_boxed` (same file) is explicit that this is a known,
deliberate scope boundary, not an oversight:

> Conservative on purpose: only unambiguous heap composites — tuples and
> `text` — are flipped to boxed. ... **Arrays, options, and generics are left
> as a future extension** once each has a verified round-trip.

So: **any** function returning `Dict`, `[T]`/Array, `Option<T>`, or a
user-defined composite type that is forced through `InterpCall` for *any*
`FallbackReason` other than the now-fixed `CollectionLiteral` (e.g.
`PatternMatch`, `Closure`, `TryOperator`, `ActorOps`, `UserMacros`,
`DynamicTypes`, ...) will hit this same corruption. The S68 fix only closed
the Dict-literal-specific door; the room is still open.

## Blast-radius check (pure-Simple compiler source)

```
$ grep -rn '\-> *Dict<\|\-> *Map<' src/compiler/ | wc -l
23   (across 17 files)
```

Representative hits: `src/compiler/00.common/effects.spl:184` (`init_builtins`),
`src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl:79`
(`module_functions_destructure`), `src/compiler/30.types/type_system/effects.spl`
(3 functions), `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:271`
(`declare_module_statics`), `src/compiler/90.tools/lint/_LintMain/config_and_model.spl`
(2 functions), and 11 more (full list reproducible with the grep above).

None of these were individually audited here for whether their *bodies* (or
their transitive callees) trip a *different* `FallbackReason`. That audit —
checking each of the 23 sites (and their callers, since the corruption
manifests at the call site, not the callee) for pattern-match/closure/try-op/
actor/macro usage that would still route them through `InterpCall` — is the
concrete next step before this class of bug can be called fully closed for the
bootstrap-relevant cranelift path.

## Recommended next step

Two independent, non-mutually-exclusive paths, same as the original S59 doc's
options A/B applied at the right layer:

1. **Keep shrinking the false-fallback surface** (the S68 approach): audit each
   remaining `FallbackReason` producer in `compilability.rs` the same way Dict
   was just audited — is it still type-blind/overly-conservative for
   constructs that already lower to native MIR? Each one removed shrinks the
   set of functions that can ever reach the broken `InterpCall` path.
2. **Fix the bridge itself**: extend `compile_interp_call` / `return_type_keeps_boxed`
   so generic/composite return types (Dict, Array, Option, struct) get a
   correct **native-handle extraction** step analogous to `rt_value_raw_i64`/
   `rt_value_as_float` — i.e. a `rt_value_as_handle`-style unwrap that pulls
   the tagged heap pointer out of the interpreter's boxed `RuntimeValue`
   instead of either leaving it boxed (current default) or blindly truncating
   it (which the doc explicitly warns against for tuple/text). This closes the
   gap at the source instead of playing whack-a-mole with fallback reasons.

## Audit (S71) — 2026-07-18

**Status:** CRITICAL — ALL 24 Dict-returning functions in the pure-Simple
compiler source are AT-RISK. All have `TryOperator` triggers; 8 have
`PatternMatch`; 6 have `AsyncAwait`. At least one (`process_async()`) is
bootstrap-critical. This is not a whack-a-mole issue — it's a categorical gap
affecting the entire class of composite-return codepaths.

### Findings

**Inventory Summary:**
```
Total Dict<T>/Map-returning functions in src/compiler/: 24
All 24 have TryOperator (.?) triggers in function bodies (50-line scan)
  - 8 also have PatternMatch (match keyword)
  - 6 also have AsyncAwait (async keyword)
Safe (no triggers): 0
AT-RISK (via other FallbackReasons): 24/24
```

**Complete AT-RISK Inventory:**

| File | Line | Function | Triggers |
|------|------|----------|----------|
| src/compiler/00.common/effects.spl | 184 | `init_builtins()` | TryOp, AsyncAwait |
| src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl | 79 | `module_functions_destructure()` | TryOp |
| src/compiler/30.types/type_system/effects.spl | 127 | `build_effect_env()` | TryOp, AsyncAwait |
| src/compiler/30.types/type_system/effects.spl | 141 | `infer_mutual_effects()` | TryOp, AsyncAwait |
| src/compiler/30.types/type_system/effects.spl | 171 | `propagate_effects_transitive()` | TryOp, AsyncAwait |
| src/compiler/30.types/type_system/_StmtCheck/bindings_check.spl | 311 | `bind_pattern()` | PatternMatch, TryOp |
| src/compiler/40.mono/monomorphize_integration.spl | 68 | `process_modules()` | TryOp |
| src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl | 1709 | `snapshot_lambda_capture()` | PatternMatch, TryOp |
| src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl | 463 | `local_use_counts()` | PatternMatch, TryOp |
| src/compiler/60.mir_opt/mir_opt/loop_detect.spl | 155 | `reachable_from()` | TryOp |
| src/compiler/60.mir_opt/mir_opt/loop_detect.spl | 176 | `can_reach_target()` | TryOp |
| src/compiler/70.backend/backend_types.spl | 365 | `as_dict()` | PatternMatch, TryOp |
| src/compiler/70.backend/backend/env.spl | 65 | `empty_env_scope()` | PatternMatch, TryOp |
| src/compiler/70.backend/backend/env.spl | 118 | `snapshot_locals()` | TryOp |
| src/compiler/70.backend/backend/cranelift_codegen_adapter.spl | 271 | `declare_module_statics()` | TryOp |
| src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl | 336 | `mark_return_chain_handled()` | PatternMatch, TryOp |
| src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl | 348 | (unnamed) | PatternMatch, TryOp |
| src/compiler/80.driver/driver_pipeline.spl | 257 | `process_async()` | TryOp, AsyncAwait |
| src/compiler/90.tools/async_integration.spl | 320 | `process_async_mir()` | TryOp, AsyncAwait |
| src/compiler/90.tools/coupling/metrics.spl | 18 | `compute_fan_out()` | TryOp |
| src/compiler/90.tools/coupling/metrics.spl | 24 | `compute_fan_in()` | TryOp |
| src/compiler/90.tools/lint/_LintMain/config_and_model.spl | 92 | `build_default_levels()` | TryOp |
| src/compiler/90.tools/lint/_LintMain/config_and_model.spl | 153 | `profile_default_levels()` | PatternMatch, TryOp |
| src/compiler/99.loader/jit_context.spl | 62 | `type_registry()` | TryOp |

### Bootstrap-Critical Path Status

- `process_async()` (driver_pipeline.spl:257) is called during the compilation
  driver's MIR processing phase (confirmed: compiler/80.driver/driver_pipeline.spl:166,
  compiler/80.driver/driver.spl:1084). This function returns
  `Dict<text, AsyncStateMachine>` with TryOp + AsyncAwait triggers.
- If native `--backend=cranelift` codegen encounters any of these functions via
  PatternMatch, Closure, or other non-CollectionLiteral fallback reasons, the
  corrupted boxed result will propagate as garbage handles into native consumers.
- Risk is **active on bootstrap path**, not hypothetical: `process_async()` is
  invoked unconditionally during driver setup.

### Fix Mechanism Sketch

**Current state (broken):**
1. `compile_interp_call()` in src/compiler_rust/compiler/src/codegen/instr/core.rs
   (~line 758–839) calls `rt_interp_call()` to invoke the interpreter, receiving
   a `RuntimeValue` (NaN-boxed u64).
2. For composite returns (Dict, Array, Option), lines 826–835 use heuristic
   checks: if `keep_boxed_result || interp_call_keeps_boxed_result(func_name)`,
   store the boxed wrapper directly (line 834). Otherwise, for non-F64,
   non-extern-bridge destinations, there is no unboxing step — the wrapped
   `RuntimeValue` is stored as-is.
3. Downstream native code (e.g., `Dict.len()`) expects a tagged heap handle
   (pointer + type tag in the u64), not a NaN-boxed wrapper, and reads garbage.

**Required fix:**
- Extend `runtime/src/value/sffi/value_ops.rs` with a new function (e.g.,
  `rt_value_as_handle`) that extracts the tagged heap pointer from a
  `RuntimeValue` NaN-box without stripping the tag.
  - Input: `RuntimeValue` (u64 in NaN-box format, tag in high bits per tags.rs)
  - Output: i64 (the same tagged handle, usable by runtime Dict/Array/Option ops)
  - Mechanism: RuntimeValue::is_heap() checks the tag; if true, extract the
    payload (lower 48 bits) and preserve the tag (upper bits).
- Wire this into `compile_interp_call()`: when `!keep_boxed_result` and the
  destination type is a user-defined composite (Dict, [T], Option<T>, class),
  call `rt_value_as_handle` instead of leaving the boxed wrapper.
- Add runtime_sffi.rs entry for the function (per runtime_symbols.rs pattern).
- Regression test: a Dict-returning function with TryOp/PatternMatch should
  round-trip through InterpCall with correct handles.

### Risk Assessment

**Scope:** The gap affects any pure-Simple function with composite return type
that is forced through InterpCall for any FallbackReason. The S68 dict-literal
fix removed *one* reason; 23 others remain (PatternMatch, TryOp, etc.).

**Severity:** Silent wrong result (handles read as garbage), affecting any
bootstrap that routes a Dict-returning function through the interp path and
then calls methods on the result.

**Recommendation:** Implement the `rt_value_as_handle` fix before any major
bootstrap with dict-using functions on the native cranelift path. Track as
a critical pre-release blocker.

## Fix (S78) — 2026-07-18

**Root cause was NOT where the S71 audit sketch guessed.** The audit's "Fix
Mechanism Sketch" proposed adding a new `rt_value_as_handle` extraction step to
`compile_interp_call` (`codegen/instr/core.rs`) or `value_ops.rs`, reasoning
that the interpreter's boxed `RuntimeValue` needed a pointer/tag extraction to
become the native tagged handle. Tracing the actual data flow end to end
disproved this:

1. `compile_interp_call` (`codegen/instr/core.rs:758-839`) already does the
   right thing for a plain (non-`rt_`/`spl_`) function whose destination vreg
   has no scalar type entry — a Dict-returning function matches this exactly
   — it falls to the final `else { result }` branch and keeps the value
   **boxed** as-is. No codegen change was needed or made.
2. `rt_interp_call` (`runtime/src/value/sffi/interpreter_bridge.rs`) already
   returns a proper `simple_runtime::RuntimeValue` — the *same* NaN-boxed
   type used everywhere in compiled code (confirmed: `rt_dict_new`/
   `rt_dict_len`/etc. all take/return `RuntimeValue` directly — there is only
   one runtime value representation, not two).
3. The actual defect: `interp_call_handler`
   (`compiler/src/interpreter_sffi.rs`) converts the interpreter's own
   `Value` enum to a `RuntimeValue` via
   `crate::runtime_bridge::value_to_runtime`
   (`compiler/src/runtime_bridge.rs`). That function's `match` had **no arm
   for `Value::Dict`/`Value::FrozenDict`** — every Dict result fell through
   to the wildcard `_ => RuntimeValue::NIL`, silently discarding the entire
   dict before it ever reached `compile_interp_call`. `rt_dict_len(NIL)`
   returns `-1` via its `as_typed_ptr!` fallback (`runtime/src/value/dict.rs`),
   matching the originally reported symptom exactly.

**Fix:** added a `Value::Dict(map) | Value::FrozenDict(map) => ...` arm to
`value_to_runtime` (`compiler/src/runtime_bridge.rs`) that marshals the dict
through `rt_dict_new`/`rt_dict_set` (keys via `rt_string_new`, values
recursively through `value_to_runtime`), mirroring the existing
`values_to_runtime_array`/`values_to_runtime_tuple` pattern. Added the
symmetric `HeapObjectType::Dict` decode arm to `runtime_to_value` (fixes the
mirror gap for Dict arguments passed *into* an `InterpCall`'d function). **No
new `rt_` extern was added** — `rt_dict_new`/`rt_dict_set`/`rt_dict_entries`
already existed and were reused.

**Identity is NOT preserved — this is a deep copy, not a pointer/tag
extraction.** The interpreter's `Value::Dict` is `Arc<HashMap<String,
Value>>`; the native `RuntimeDict` (`runtime/src/value/dict.rs`) is a
separate heap allocation with a different memory layout. There is no shared
underlying object to extract a handle from. This is correct for a *return
value*: the interpreter-side dict returned by a freshly-called function has
no other alias, so a deep copy loses no shared-mutation semantics. It mirrors
exactly how `Value::Tuple`/`Value::Array` were already handled before this
fix (`values_to_runtime_tuple`/`values_to_runtime_array`).

**Still open:** `value_to_runtime` still has no arm for `Value::Object`
(class/struct instances — would need a class-id registry lookup that does
not currently exist as a simple callable path) or `Value::Enum` (covers
`Option`). Both still fall to `_ => RuntimeValue::NIL`. This means
`process_async()`'s `Dict<text, AsyncStateMachine>` (bootstrap-critical,
`driver_pipeline.spl:257`) is **only partially fixed**: the outer Dict now
marshals correctly, but if any *value* inside it is an `Object`/`Enum`
instance, that value still collapses to NIL. `Dict<text, i64>` /
`Dict<text, text>` / `Dict<text, [T]>` (scalars, strings, arrays, nested
dicts) round-trip correctly; `Dict<text, SomeClass>` does not yet.

**Verification:**
- **Load-bearing proof — unit A/B directly on the bridge conversion
  function:** with the `Value::Dict(map) | Value::FrozenDict(map) => ...` arm
  in `value_to_runtime` temporarily disabled (falling back to the pristine
  `_ => RuntimeValue::NIL`), the new `runtime_bridge.rs` tests fail exactly as
  predicted — `rt_dict_len(runtime) == -1` (the exact reported symptom) and
  `rt_dict_contains`/`rt_dict_get` on the "dict" also fail, because the value
  is really `NIL`, not a dict. Restoring the arm makes all three pass. This
  is the direct, empirical before/after proof of the fix, on the exact code
  path the interpreter bridge uses.
- New unit tests in `compiler/src/runtime_bridge.rs` (`value_to_runtime_dict_*`,
  `dict_runtime_to_value_roundtrip`, `frozen_dict_also_marshals_to_native_dict`)
  and `compiler/src/mir/hybrid.rs`
  (`dict_returning_function_with_try_operator_still_routes_through_interp_call`).
- `cargo test -p simple-compiler --lib` targeted families (runtime_bridge,
  mir::hybrid, compilability, codegen) all green except pre-existing,
  unrelated failures verified via file-swap A/B against pristine HEAD
  (identical failing-test-name sets before/after, byte-for-byte, for the
  `codegen` family: 143/143). A full `--lib` run on the fixed tree (3110
  passed, 249 failed) vs. a full `--lib` run on pristine HEAD (3104 passed,
  249 failed) has an **empty failing-test-NAME diff in both directions** —
  zero regressions introduced by the `runtime_to_value` Dict-decode addition,
  and (expectedly) zero pre-existing failures incidentally fixed.
- **End-to-end (inconclusive, documented honestly):** attempted a repro
  `.spl` (Dict-returning function using `.?` inside to force
  `FallbackReason::TryOperator`, called from a native `main`) via
  `native-build --backend cranelift` (`SIMPLE_NATIVE_BUILD_RUST=1` to use the
  Rust seed handler directly). Both the pre-fix and post-fix binaries exited
  `2` (the correct `len()`) — the e2e did **not** reproduce a 255→2
  transition. Instrumenting `interp_call_handler` with a trace `eprintln!`
  confirmed why: it never fired for this build, meaning `native-build`'s
  AOT/`--entry-closure` path compiled the whole `.?`-containing function
  natively and never routed the call through `InterpCall`/`rt_interp_call` at
  all, so the interpreter bridge (and this fix) was never exercised by that
  vehicle. The bridge is live on the JIT/`SIMPLE_BOOTSTRAP` hybrid-execution
  paths (the three `apply_hybrid_transform` call sites in
  `compiler/src/pipeline/execution.rs`) — not on a leaf `native-build` of a
  two-function file — which is where the 24 audited functions and
  `process_async()` actually take this path during a real bootstrap. The
  unit A/B above, on the exact conversion function the bridge calls, is the
  proof of record for this fix; the e2e attempt is reported for
  transparency, not as supporting evidence.

## Fix (S82) — 2026-07-18

Closed the two residuals S78 left open: `value_to_runtime` (and its symmetric
decode, `runtime_to_value`) had no arm for `Value::Enum` or `Value::Object`,
so both still fell through to the wildcard `_ => RuntimeValue::NIL`
(encode)/`Value::Nil` (decode).

### Representation analysis (with citations)

**Interpreter side** (`compiler/src/value.rs`):
- `Value::Enum { enum_name: String, variant: String, payload: Option<Box<Value>> }`
  (`value.rs:924-928`).
- `Value::Object { class: String, fields: Arc<HashMap<String, Value>> }`
  (`value.rs:920-923`).

**Native side, Enum** (`runtime/src/value/objects.rs`):
- `RuntimeEnum { header: HeapHeader, enum_id: u32, discriminant: u32, payload: RuntimeValue }`
  (`objects.rs:74-84`), allocated by `rt_enum_new(enum_id, discriminant, payload)`
  (`objects.rs:260-278`).
- The discriminant is `hash_variant_discriminant(variant_name)` — a
  `DefaultHasher` hash of the **variant name string alone** (`objects.rs:250-257`).
  This is the *only* thing native code ever checks: `compile_pattern_test`'s
  `MirPattern::Variant` arm compares `rt_enum_discriminant(subject)` against
  a hashed expected variant name and nothing else
  (`compiler/src/codegen/instr/pattern.rs:70-85`, hasher at `pattern.rs:117-124`,
  byte-identical to `variant_disc` in `codegen/instr/result.rs:12-19`).
  `rt_is_none`/`rt_is_some` (`objects.rs:317-344`) likewise dispatch only on
  discriminant.
- `enum_id` is **not read anywhere for correctness** — confirmed empirically:
  `compile_enum_unit`/`compile_enum_with` (`codegen/instr/pattern.rs:126-154`,
  the path used for every non-Option/Result enum construction) hardcode
  `enum_id = 0` unconditionally; `rt_option_map` (`objects.rs:349-373`)
  hardcodes `enum_id = 0` when re-wrapping a fresh `Some`; only
  `create_enum_value` in `codegen/instr/result.rs:21-41` (used solely for
  Option/Result) passes `enum_id = 1` for Option / `0` for Result
  (call sites at `result.rs:80,84,93,102`). Three different producers, three
  different (inconsistent) conventions, and none of it is ever read back —
  `rt_enum_id` (`objects.rs:287-290`) is exercised only by direct unit tests
  (`compiler/src/pipeline/native_project/tests.rs:1949,1988,5027`), never by
  codegen decision-making. This means discriminant-only identity is
  sufficient for a sound Enum marshal — no class/enum-id registry is needed
  for this half of the gap, unlike Object below.

**Native side, Object** (the actual finding that explains S78's "no
class-id registry lookup exists" note): `RuntimeObject`/`rt_object_new`
(`objects.rs:43-52,90-114`, `HeapObjectType::Object`) is a real,
fully-implemented heap-header representation with `class_id`/`field_count`/
indexed fields — **but the native cranelift codegen path never uses it for
class instances.** `compile_struct_init`
(`compiler/src/codegen/instr/closures_structs.rs:206-248`) instead
`rt_alloc`s a raw block and writes each field at a compile-time-baked-in
byte offset (`field_offsets: &[u32]`, from `MirInst::StructInit`), optionally
prefixing a vtable pointer at offset 0, then tags the pointer with the bare
`TAG_HEAP` bit (`heap_tag = 1`, `closures_structs.rs:245-246` — note
`TAG_HEAP == 0b001` in `runtime/src/value/tags.rs:5`, so this **is**
heap-tagged, but carries no `HeapHeader`/`HeapObjectType` prefix at all).
There is no runtime-queryable "class name/id → field layout" table anywhere
in the codebase; the layout is a MIR-level compile-time fact
(`MirInst::StructInit { field_offsets, field_types, .. }`) that never
round-trips through anything the bridge could consult at the
`interp_call_handler` boundary. `rt_object_new` is registered as an SFFI
symbol (`codegen/runtime_sffi.rs`, `elf_utils.rs:585`) but is not called from
any `codegen/instr/*.rs` call site — grep confirms zero producers on the
native path. Even were a name→id table added, converting a `Value::Object`
into a real `RuntimeObject` would be **actively unsound**: a class's native
consumers expect the bare offset-based layout, not `RuntimeObject`'s
header+class_id+field_count preamble, so every field read downstream would
be misaligned. Object marshaling is therefore not implementable at this
bridge layer at all without a broader design change (e.g. threading a
compile-time-generated layout table through to runtime, which does not
exist today and is out of scope for a bridge-layer fix).

### What was implemented

- **Enum (encode, `value_to_runtime`):** full support for any `Value::Enum`
  (built-in Option/Result and user-defined), via
  `rt_enum_new(enum_id, hash_variant_discriminant(variant), payload_rv)`.
  `enum_id` is set to 1 for `Option` / 0 otherwise purely to match the native
  convention noted above — it is decorative, not load-bearing. This is the
  fix that matters: it makes any Option/Result/enum-returning function that
  gets forced through `InterpCall` (TryOperator, PatternMatch, etc. — the
  S71-audited 24 Dict-returning functions and any Option/Result-returning
  sibling) round-trip correctly to native `rt_is_none`/`rt_is_some`/pattern
  matching, instead of silently becoming `NIL` (which native code reads as
  `None`/falsy regardless of the real value — the exact silent-corruption
  class this whole bug chain is about).
- **Enum (decode, `runtime_to_value`):** precise reconstruction for the four
  well-known Option/Result discriminants (`Some`/`None`/`Ok`/`Err`) by
  comparing against `hash_variant_discriminant` of each known name. For any
  other discriminant (an arbitrary user-defined enum), the variant/enum name
  cannot be recovered from a one-way hash with no reverse registry — this
  path now **panics loudly** (naming the discriminant) instead of returning
  a silently-wrong `Value::Nil`, per the S82 mandate to convert unrecoverable
  silent corruption into loud failure.
- **Object (both directions):** no marshal is attempted (see the soundness
  argument above). Both `value_to_runtime`'s `Value::Object` arm and
  `runtime_to_value`'s `HeapObjectType::Object` arm now `panic!` with the
  class name (encode side) or `class_id` (decode side, via
  `rt_object_class_id`), replacing the prior silent `NIL`/`Nil` collapse.

### Registry-gap writeup for the follow-up

Two distinct, independent gaps remain, both requiring a compile-time-to-
runtime layout table that does not exist today:
1. **Object marshal (both directions):** would need the compiler to emit a
   `class_id -> (field_name, offset, type)*` table reachable at runtime (or
   change `compile_struct_init` to use the existing `RuntimeObject`
   representation instead of raw offset structs), plus a symmetric decode.
   Until then, any function forced through `InterpCall` that returns/accepts
   a class instance will panic at the bridge rather than silently corrupt —
   tracked here as the concrete next step.
2. **Enum decode for arbitrary (non-Option/Result) user enums:** would need
   either (a) a reverse `discriminant -> (enum_name, variant_name)` table
   populated at enum-construction time, or (b) widening the wire format
   (e.g. embedding the name string in the payload for interp-bridge crossings
   only), both of which are out of scope for this bridge-layer fix and would
   need their own design review given they'd touch the hot construction path
   for every enum literal in the compiler.
3. **Pre-existing, adjacent (not introduced by S82):** `runtime_to_value`'s
   generic `TAG_HEAP` dispatch (`runtime_bridge.rs`, the `unsafe { let header
   = ptr.cast::<HeapHeader>(); ... }` block) assumes every heap-tagged
   `RuntimeValue` is `HeapHeader`-prefixed. A native class instance from
   `compile_struct_init` is heap-tagged but is NOT `HeapHeader`-prefixed
   (see above), so if one is ever passed as an `InterpCall` argument, this
   dispatch reads whatever raw field bytes happen to sit at the header
   offset as a `HeapObjectType` discriminant — undefined behavior that
   predates this fix and is out of scope for it, but is documented here so
   the next lane doesn't have to re-derive it.

### Test evidence

- New unit tests in `compiler/src/runtime_bridge.rs`:
  `value_to_runtime_option_some_is_a_real_native_enum_not_nil`,
  `value_to_runtime_option_none_is_recognized_as_none_discriminant`,
  `value_to_runtime_result_ok_and_err_round_trip_discriminant`,
  `option_some_runtime_to_value_roundtrip`,
  `option_none_runtime_to_value_roundtrip`,
  `result_ok_err_runtime_to_value_roundtrip`,
  `value_to_runtime_dict_with_nested_option_round_trips` (the S71-flagged
  "Dict of Enum" nesting case), `value_to_runtime_object_panics_loudly_instead_of_silently_nil`,
  `runtime_to_value_object_panics_loudly_instead_of_silently_nil`,
  `runtime_to_value_unknown_enum_discriminant_panics_loudly_instead_of_silently_nil`.
- `cargo test -p simple-compiler --lib runtime_bridge -- --test-threads=1`:
  21 passed, 1 failed (`test_value_to_runtime_array` — the pre-declared,
  pre-existing upstream failure from the ANY-erasure work, owned by another
  lane; unrelated to this change and not grown by it), 0 new failures.
  All S78 Dict tests remain green.
- **Full-suite before/after, file-swap A/B against pristine `356a3c058dc`**
  (same methodology as S78): with `compiler/src/runtime_bridge.rs` swapped
  back to the pristine (pre-S82) content, `cargo test -p simple-compiler --lib`
  reports **3117 passed; 248 failed; 1 ignored** (finished in 144.98s). With
  the S82 changes restored, the same command reports **3127 passed; 248
  failed; 1 ignored** (finished in 152.01s) — exactly 10 more passing tests
  (the 10 new tests this fix adds), the *same* failed count, and a
  byte-for-byte **empty failing-test-NAME diff in both directions**
  (`comm -23`/`comm -13` on the sorted 248-line failing-name lists from each
  run both print nothing). This is the check that specifically matters for
  this change (unlike S78's NIL→value fix, S82 also introduces two new
  `panic!` arms on the *decode* side — `HeapObjectType::Object` and
  unrecognized-discriminant `HeapObjectType::Enum` in `runtime_to_value`,
  which is reached when native code passes an argument *into* an
  `InterpCall`'d function): an empty diff confirms no test in the full
  `--lib` suite exercises a native Object or unknown-enum argument through
  this decode path, so converting those two silent-NIL branches into loud
  failures introduces zero observable regressions against the current test
  suite.

## Related

- `doc/08_tracking/bug/s59_cranelift_dict_return_abi_root_cause_2026-07-17.md`
- `doc/08_tracking/bug/seed_native_cranelift_dict_return_abi_2026-07-17.md`
- Fix landed alongside this doc: `compiler/src/compilability.rs` (`Expr::Dict`
  no longer adds `FallbackReason::CollectionLiteral`), plus regression tests in
  `compiler/src/compilability.rs` and `compiler/src/mir/hybrid.rs`.

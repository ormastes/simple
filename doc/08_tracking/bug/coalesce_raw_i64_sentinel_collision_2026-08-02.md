# `??` on a raw i64 treats the value 3 as nil (JIT sentinel collision)

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Engines:** JIT only. Interpreter was always correct. Standalone native fails
  closed (see "Native scope correction").
- **Memory ref:** `reference_coalesce_on_raw_i64_corrupts_index_3`

## Symptom

Under the JIT (`bin/simple run`, default engine), `x ?? default` on a raw
(non-optional) `i64` returns `default` when `x == 3`:

```simple
val xs = [0, 1, 2, 3, 4, 5]
xs[3] ?? -1        # JIT: -1 (wrong). Interpreter: 3 (correct).
val a: i64 = 3
a ?? 99            # JIT: 99 (wrong). Interpreter: 3 (correct).
```

Typical real-world hit: `xs.index_of(v) ?? -1` silently corrupting index 3.

## Root cause

`lower_coalesce` in
`src/compiler_rust/compiler/src/hir/lower/expr/control.rs` lowered every
`expr ?? default` to `if expr != nil then rt_unwrap_or_self(expr) else default`
regardless of the operand's static type. The runtime nil sentinel is the raw
integer 3 (`TAG_SPECIAL = 0b011` with an empty payload; see
`codegen/instr/helpers.rs`, `codegen/instr/pattern.rs`,
`mir/lower/lowering_expr_literal.rs`), and the JIT's `!= nil` comparison on an
untagged scalar is a plain integer compare against that sentinel — so the
legitimate value 3 tested equal to nil and took the else branch. The interpreter
carries a real type tag, so it never collided.

`HirType` has no Optional variant, so the check could not tell an Option from a
raw `i64` in the first place.

## Fix

Type-directed, not a literal-3 special case. In `lower_coalesce`: when the left
operand's static type is a non-nullable scalar (`BOOL`, `I8`–`I64`, `U8`–`U64`,
`F32`, `F64`, `CHAR`), `??` is the identity — lower directly to the left operand
with no runtime nil check, since such a value can never legitimately be nil and
the check could only ever do harm. `STRING`/`ANY`/`UNKNOWN` and all registered
types (including `T?`, which resolves to a Pointer TypeId) keep the runtime
check. Debug visibility via `SIMPLE_DEBUG_COALESCE=1` (level-gated, default off).

### The exception the first pass missed — a live regression, now closed

The first pass shipped with a "known caveat" about `first`/`last`/`get` being
typed bare `T` while genuinely optional. That caveat was **not benign**. The
method result-type table in `hir/lower/expr/mod.rs` types several genuinely
optional accessors as bare `T` — `[T].first/last/get/min/max/pop` and
`{K:V}.get/remove` — so keying the shortcut on the scalar `TypeId` alone
regressed them. Measured on the first-pass binary:

```
val empty: [i64] = []
empty.first() ?? -1        # before any fix: -1 (correct).  first pass: 3  WRONG
val d: {text: i64} = {}
d.get("k") ?? -1           # before any fix: -1 (correct).  first pass: 3  WRONG
```

The raw sentinel `3` leaked out as an ordinary integer — strictly worse than the
bug being fixed, and invisible to `SIMPLE_DEBUG_COALESCE` because those operands
legitimately report `ty=TypeId(5)` (`i64`). Those accessors are now excluded from
the shortcut and keep the runtime nil check.

### Why the accessors were not retyped to `T?` instead

Retyping them to `HirType::Pointer` (what `at` already does) is the
type-system-level root fix, tracked in
`doc/03_plan/compiler/type_system/seed_hirtype_optional_plan.md`. It was
**measured and rejected for now**: `at` itself is currently broken in value
position on the JIT while `first` is correct, so moving the widely-used
accessors onto that lane today would import a larger defect than it removes.

```
val xs = [9, 8, 7]
xs.at(0)              -> <enum@0x2e92a930e40>     xs.first()              -> 9
val a: i64 = xs.at(1) -> 3200464915713            val f: i64 = xs.first() -> 9
xs.at(0) + 1          -> 0.0000...15812397653996  xs.first() + 1          -> 10
```

Fixing `at`'s value-position lowering is the precondition for the retyping step.

## Which values collide

Swept `-5, -3, -1, 0, 1, 2, 3, 4, 5, 8, 10, 11, 12, 16, 18, 19, 20, 24, 27`
through `v ?? 987654` on the unfixed JIT: **only `3`**. `0` and negatives are
unaffected. The tagged bool encodings (`false = 19`, `true = 11`) do **not**
collide on the `i64` lane, because the emitted comparison is an exact `!= 3`
rather than a tag-bits test. A `char` of code 3 collides for the same reason and
is covered by the same type-directed fix.

## Native scope correction

The original report said the standalone native ELF backend was affected too. It
is **not reachable**: `compilability.rs` flags `Expr::Coalesce` as
`FallbackReason::TryOperator`, so `simple compile <f>.spl --native` **refuses**
the program ("1 function(s) contain constructs that require the interpreter:
main: [TryOperator]") rather than miscompiling it. Native fails closed here.

The pure-Simple `native-build` lane could not be measured in the working copy
used for this fix: it aborts with `semantic: unknown extern function:
rt_host_arch_name`, from an unrelated in-flight edit to
`src/lib/nogc_sync_mut/io/env_ops.spl`.

## Known remaining gap (separate defect, unchanged)

`[3].first() ?? -1` still yields `-1`, and a declared `val v: i64? = 3` still
reads as `None` on the JIT. That is the separate flat-`T?`-lane collision
(`reference_jit_option_i64_value3_none_collision`,
`jit_option_i64_value3_reads_as_none_2026-07-24.md`) — the same sentinel one
layer down, inside the Option encoding — and is unchanged by this fix in either
direction.

## Verification (2026-08-04)

Hand-computed expectations, not engine agreement. Built with
`cargo build -p simple-driver --bin simple`; probes run through the resulting
binary's JIT with the tree-walk interpreter as the cross-check.

| case | before | first pass | after | expected |
|------|--------|-----------|-------|----------|
| `xs[3] ?? -1` on `[0..5]` | `-1` | `3` | `3` | `3` |
| `val n = 3; n ?? 987654` | `987654` | `3` | `3` | `3` |
| `char` code 3 | `987654` | `3` | `3` | `3` |
| `[].first() ?? -1` | `-1` | **`3`** | `-1` | `-1` |
| `{}.get(k) ?? -1` | `-1` | **`3`** | `-1` | `-1` |
| `[9,8].first() ?? -1` | `9` | `9` | `9` | `9` |
| `(nil: text?) ?? "D"` | `D` | `D` | `D` | `D` |

Sabotage control, both arms rebuilt from source:

- disable the whole shortcut → `test_coalesce_on_raw_scalar_emits_no_nil_check`
  FAILS, other two pass (exit 101).
- disable only the optional-accessor guard →
  `test_coalesce_on_optional_accessor_keeps_nil_check` FAILS, other two pass
  (exit 101).
- restore → 3 passed, 0 failed (exit 0).

## Regression guards

`src/compiler_rust/compiler/src/hir/lower/tests/control_flow_tests.rs`:
`test_coalesce_on_raw_scalar_emits_no_nil_check`,
`test_coalesce_on_optional_accessor_keeps_nil_check`,
`test_coalesce_on_declared_optional_keeps_nil_check`.

A behavioural `.spl` spec cannot guard this: `bin/simple test` hard-defaults to
the tree-walk interpreter, which was always correct here, so such a spec stays
green on a fully broken JIT.

## Update 2026-08-17: the "known remaining gap" was the SAME bug as the OOB one, and is now root-caused

This doc's closing section left `[3].first() ?? -1` yielding `-1` as a separate
"flat-`T?`-lane collision". It is not separate. It is the same defect as
`doc/08_tracking/bug/jit_array_oob_read_leaks_raw_rt_nil_sentinel_2026-08-07.md`,
seen from the other side, and both trace to one line of the method result-type
table this doc already fingered but chose not to change:

  `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:1478`
  `"first" | "last" | "get" | "max" | "min" => Some(*element)`
  (and `:1601` for dict `get`/`remove`)

Because these genuinely-optional accessors are typed as the bare element type,
`needs_int_unbox` in
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:600-617`
unboxes their result to a RAW i64 before anything inspects it. That is what
makes the `!= nil` check this doc's fix deliberately RETAINED for those
accessors (`control.rs:1815-1847`) a raw-integer compare against 3 — precisely
the hazard the rest of the fix removed, just relocated onto the accessor lane.
The same unbox is why a MISS formats as the integer `3` instead of `nil`.

Measured 2026-08-17 on a seed built from HEAD (JIT arm):

```
FAIL present_3_get_coalesce got=-1 want=3      # ys=[1,2,3]; ys.get(2) ?? -1
FAIL present_3_first got=-1 want=3             # [3,4].first() ?? -1
FAIL present_3_last got=-1 want=3              # [4,3].last() ?? -1
FAIL present_3_dict_coalesce got=-1 want=3     # {"k":3}.get("k") ?? -1
FAIL array_get_miss_bare got=3 want=nil        # the other direction
```

The direction this doc DID fix stays fixed — `raw_coalesce_3`,
`raw_coalesce_computed3`, `raw_coalesce_neg3`, `raw_coalesce_u8_3`,
`raw_coalesce_i32_3` and the 0/11/19/24 neighbours all PASS on the same binary.

Fix: type those accessors `TypeId::ANY` so the value stays BOXED (nil = word 3,
present 3 = word 24, distinguishable). This does NOT require the `T?`/`Pointer`
retyping that this doc measured and rejected, and so does not depend on `at`'s
broken value-position lowering being fixed first.

Class-level regression fence (subprocess-based, since spec bodies run
interpreted and the interpreter is correct here):
`test/01_unit/compiler/codegen/rt_nil_sentinel_collision_class_spec.spl`

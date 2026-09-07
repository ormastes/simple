# JIT: `.is_some()` / `.is_none()` method calls fail closed OR return a raw untagged bool

- **ID:** jit_is_some_is_none_method_dispatch_gap
- **Date:** 2026-08-17
- **Status:** OPEN (P1)
- **Severity:** high — one shape is a silent wrong result (`nil` where `true`
  belongs), the other is a hard stop. Both on the default `bin/simple run` lane.
- **Component:** seed JIT method dispatch,
  `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1904`
- **Lane:** Rust bootstrap seed, cranelift JIT. The tree-walk interpreter is
  CORRECT — this is a cross-engine divergence.

## How it was found

Not filed from a report. It surfaced as residual failures in the run-path probe
`test/01_unit/compiler/codegen/probe_option_presence_falsy_payload.spl`, written
for a *different* defect (the `rt_is_none` zero/nil bit-pattern collision, see
Cross-refs). Once that fix landed, 4 of the original 9 JIT failures survived —
and they behaved differently from the rest: **wrong for PRESENT and ABSENT
receivers alike**, which is what proves they are not a presence bug.

## Reproduction

Against a seed freshly built from `88227f48202` **plus** the `rt_is_none` fix
(so this is not that defect leaking through):

```simple
fn zero_i64() -> i64?:
    return 0

fn main() -> i64:
    val o: i64? = 0
    print(o.is_some())     # JIT: Runtime error: Function 'is_some' not found (exit 70)
    print("ab".contains("a"))   # JIT: true  <- CONTROL: bool boxing works generally
    return 0
```

Shape A — **fails closed** when the receiver is a plain local:

```
Runtime error: Function 'is_some' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not
a program error. Refusing to substitute a placeholder value (...)
exit 70
```

Shape B — **silently wrong** when the receiver is a function-call result
(`zero_i64().is_some()`), as measured by the probe before these rows were
removed from it:

| expression | JIT | interpreter (correct) |
|---|---|---|
| `zero_i64().is_some()` | `nil` | `true` |
| `zero_i64().is_none()` | `0` | `false` |
| `absent_i64().is_some()` | `0` | `false` |
| `absent_i64().is_none()` | `nil` | `true` |

## Root cause

`closures_structs.rs:1904` lowers the call correctly — it invokes `rt_is_some`
and the runtime helper returns the right answer — but then does:

```rust
let bool_result = builder.inst_results(call)[0];
let result = builder.ins().sextend(types::I64, bool_result);
return Ok(Some(result));
```

That yields a **raw** `0`/`1`, not a tagged `RuntimeValue`. Runtime tags live in
the low 3 bits, so a raw `1` is `0b001` = `TAG_HEAP` and renders as `nil`
(or as an invalid heap reference), while a raw `0` happens to coincide with
boxed integer zero and renders as `0`. That is precisely the tag-confusion
family: a raw scalar deposited in a slot whose reader expects a tagged word.

The `is_ok` / `is_err` arm immediately below (`:1913`) and the arm at `:1896`
use the identical `sextend` idiom and are very likely affected the same way —
**not verified here**, and deliberately not asserted anywhere yet.

Note the tension a fix must resolve: this same lowering feeds both
`if x.is_some():`, where a raw `0`/`1` is what the branch wants, and
`print(x.is_some())`, where a tagged bool is what the renderer wants. The
working control (`contains`, `starts_with`, which print `true` correctly under
JIT) reaches the result through a different path and is the model to follow.
A blind `sextend` -> "box as TAG_SPECIAL bool" swap without checking the
condition-position consumers would trade this bug for a wrong-branch bug.

## Why no spec asserts it yet

The four rows were REMOVED from
`probe_option_presence_falsy_payload.spl` rather than left red, with an inline
comment pointing here, so that probe stays a clean gate for the defect it was
written for. Re-add them when this is fixed — the probe already has the right
shape and the absent/present controls.

## Cross-refs

- `doc/08_tracking/bug/seed_interp_option_match_falls_through_at_scale_2026-07-18.md`
- `doc/08_tracking/bug/parse_family_strips_option_jit_native_2026-08-02.md`
  (both fixed by the `rt_is_none` change that exposed this one)

## Re-verified 2026-08-17 — STILL OPEN (seed defect, not fixable in .spl)

Binary identity:

```
$ readlink -f bin/simple
/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple
$ stat -c '%s %y' "$(readlink -f bin/simple)"
59537240 2026-08-17 12:58:51.339525019 +0000
```

Repro (`r1b.spl`: `zero_i64()`/`absent_i64()` returning `i64?`, four
`.is_some()`/`.is_none()` prints):

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple run r1b.spl
true
false
false
true
$ SIMPLE_EXECUTION_MODE=jit bin/simple run r1b.spl
Runtime error: Function 'is_some' not found
Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not a program error. Refusing to substitute a placeholder value (...)
```

**Update to the shape taxonomy:** Shape B (silently-wrong on a function-call
receiver) no longer reproduces — the function-call receiver now ALSO fails
closed, same as Shape A. So the current live symptom is uniformly a hard stop,
never a silent wrong value. The `sextend` arms are not even reached; dispatch
fails before them. Confirmed still present, at shifted line numbers:
`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:1905`
(`is_none`, sextend at `:1912`), `:1915` (`is_some`, sextend at `:1922`),
`:1925` (`is_ok`/`is_err`, sextend at `:1941`).

**Not fixed here:** the defect is entirely in the Rust bootstrap seed
(`src/compiler_rust/**`), so it is out of scope for a pure-Simple fix. Recorded,
not guessed at.

## RESOLVED 2026-09-06 (Rust seed, JIT/Cranelift lane) — two independent causes

**Status: FIXED. Both shapes.** Header `Status: OPEN (P1)` is superseded.

Measured on aarch64 with the seed at
`bin/release/aarch64-unknown-linux-gnu/simple`, both shapes were live
simultaneously — which is why the taxonomy above kept flip-flopping between
them. They are two DIFFERENT defects that happen to share a symptom surface.

### Shape A (hard stop) — the runtime symbol was never DECLARED

Not a dispatch gap. `ensure_runtime_functions_declared`
(`codegen/common_backend.rs`) declares a runtime import only when its name is in
the MIR's `referenced_call_names` **or** in `runtime_symbol_is_codegen_root`.
The `.is_some()` arm synthesizes `rt_is_some` from a `MethodCallStatic` whose
`func_name` is the SIMPLE name `"is_some"` — `rt_is_some` appears nowhere in the
MIR. It was not a codegen root, so `runtime_funcs.get("rt_is_some")` returned
`None`, the arm bailed with `Ok(None)`, and the caller emitted
`rt_function_not_found("is_some")`.

That also explains the INTERMITTENCE that made this look like dispatch: a
program whose closure happens to name `rt_is_some` in its own MIR (anything
pulling in `parse_i64`, for instance) gets the symbol declared as a side effect
and the arm fires normally. `rt_contains` — the working control this record
already identified — differs in exactly one respect: it has always been in the
codegen-root list.

**Fix:** add `rt_is_some` and `rt_is_none` to `runtime_symbol_is_codegen_root`.

Scoped to those two, and measured that way. `rt_enum_check_discriminant` (the
sibling `is_ok`/`is_err` arm) was added and then **removed again**: a genuine
`Result` receiver is lowered earlier and emits `rt_enum_check_discriminant` as a
real MIR `Call` — `SIMPLE_DUMP_MIR` shows six of them in the probe below — so it
is already in `referenced_call_names` and the entry would be dead. A unit test
now asserts it is NOT rooted, so re-adding it has to come with a repro.

### Shape B (silent `nil` / `0`) — HIR typed the result ANY, so MIR never boxed it

The `sextend` idiom this record blamed is fine on its own; what was missing was
a TYPE. `SIMPLE_DEBUG_METHOD_DISPATCH=1` showed:

```
[HIR-METHOD-RET] .is_some recv_ty=TypeId(18) recv_hir=Some(Pointer { .. }) -> TypeId(14) (Some(Any))
```

`TypeId(14)` is `ANY`. With an ANY result, MIR emits no boxing, and
`codegen/instr/core.rs`'s print arm passes the vreg RAW to `rt_println_value`
— raw `1` = `0b001` = TAG_HEAP renders `nil`, raw `0` collides with boxed
integer zero and renders `0`. `.contains()` never showed this because HIR
already types it `BOOL`, so MIR boxes it.

**Fix:** in `hir/lower/expr/mod.rs::lookup_method_return_type_inner`, type
`is_some`/`is_none` as `BOOL` when the receiver is a flat-nullable
`HirType::Pointer` — the same receiver shape and the same placement as the
existing `unwrap`/`expect` rule directly above it.

`is_ok`/`is_err` are deliberately NOT in that list: their receivers are genuine
`Result<T, E>` **enums**, never `Pointer`, so the arm would be unreachable for
the shapes those methods are actually used with. Verified rather than assumed —
`is_ok`/`is_err` on a real `Result` render `true`/`false` correctly on both
engines on the UNMODIFIED seed as well as the fixed one (probe
`_scratch/p_res.spl`), i.e. that path was never part of this defect.

This resolves the tension the record flagged (`if x.is_some():` wants a raw
`0`/`1`, `print(x.is_some())` wants a tagged bool): it is a **type-only**
upgrade. The emitted value is untouched, so branch position keeps consuming the
raw word.

A third candidate change — adding these names to
`builtin_method_result_type`'s BOOL arm — was written, built, and then
**reverted after measurement**: with the two fixes above in place it changed
nothing observable, and unused code is not kept.

### Evidence

`_scratch/p_opt3.spl` covers branch position, value position, negation and the
falsy-payload `Some(0)` case.

```
BEFORE (deployed seed, JIT):
  Runtime error: Function 'is_some' not found
  Runtime error: unresolved symbol ...                       (exit 70)

AFTER (seed rebuilt from this fix) — JIT output, byte-identical to the
interpreter oracle for the same file:
  A_BRANCH=some   Z_BRANCH=some   B_BRANCH=none   B_ISNONE=yes
  A_VAL=true      B_VAL=false     A_NOT_NONE=ok
```

And the record's own four-row table, JIT lane:

| expression | before | after | interpreter |
|---|---|---|---|
| `.is_some()` on present | `nil` | `true` | `true` |
| `.is_none()` on present | `0` | `false` | `false` |
| `.is_some()` on absent | `0` | `false` | `false` |
| `.is_none()` on absent | `nil` | `true` | `true` |

Rust regression tests (all pass):
`codegen::common_backend::tests::option_presence_predicate_runtime_symbols_are_retained`
(with `rt_contains` as the always-rooted control, and a negative assertion that
`rt_enum_check_discriminant` stays unrooted),
`hir::lower::tests::seed_regression_tests::flat_nullable_presence_predicates_are_bool_not_any`
(`is_some` and `is_none`), and
`hir::lower::tests::seed_regression_tests::presence_predicate_bool_typing_does_not_leak_to_other_receivers`
(a user-declared `is_some` on a class receiver keeps its own type).

Whole-crate `cargo test --release -p simple-compiler`: 3959 passed, **the same
16 pre-existing failures** as the unmodified tree (identical name sets, diffed;
all in `interpreter_extern::vulkan`, `linker`, `pipeline::execution` and
`pipeline::native_project` — none in codegen or hir).

### Re-add the removed probe rows — and a warning about running that probe

`test/01_unit/compiler/codegen/probe_option_presence_falsy_payload.spl` had four
rows removed with a pointer here. They should now go back — NOT done in this
change, because that probe belongs to the pure-Simple lane and this worktree
only rebuilt the seed.

**Do not read that probe's current green as JIT evidence.** Run through the
fixed seed with the JIT lane explicitly selected it still prints
`OPTION_PRESENCE_FALSY_PAYLOAD PROBE: ALL PASS`, but the lines above it say:

```
[CODEGEN-AMBIGUOUS-METHOD] in 'main' bare method 'to_string' has 4 candidates:
  [IoError.to_string, IoErrorKind.to_string, IoErrorKind_dot_to_string, IoError_dot_to_string]
[INFO] JIT compilation failed, falling back to interpreter
```

The whole module dropped to the interpreter on an unrelated ambiguity, so every
row in it was evaluated by the tree-walk engine. Its ALL PASS is vacuous as JIT
evidence. That ambiguity has to be resolved before the re-added rows can gate
anything on this lane.

### Still open, adjacent

`Option<ClassInstance>` receivers still mis-resolve: `.is_some()` on a
`Dict.get()` result of class type binds as `Counter.is_some` and fails closed.
That is a receiver-resolution defect (the payload type is used as the receiver
type), distinct from both shapes above, and is NOT fixed here.

### Lane coverage

JIT (Cranelift) only. `native-build` is unreachable on this host — it fails with
`native-capsule-receipt-invalid` for the unmodified seed too. The LLVM backend
has its own `"is_some" => Some("rt_is_some")` mapping
(`codegen/llvm/functions/calls.rs:2287`) and was not exercised.

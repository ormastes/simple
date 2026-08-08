# HOSTED native `.?` / if-val Option unwrap leaks the Some tag instead of the payload

**Date:** 2026-07-19
**Status:** RESOLVED 2026-07-20 for i64/text/struct/None — root-fixed and
verified on a REBUILT, RUN native-build executable (not just source-text
regression). f64/f32 payload **encode** is also root-fixed and verified
bit-correct in the emitted LLVM IR; f64/f32 payload **decode/consumption** is
source-fixed at the `if val` binding boundary, with rebuilt execution pending
(see "f64/f32 decode" below). Bool was already correct (never affected).
**Severity:** P1 — silent miscompile (wrong value, no diagnostic) on a
first-class language construct.
**Component:** compiler codegen — Option/`.?` (try-op) + `if val` binding
lowering, **hosted** native-build (`x86_64-unknown-linux-gnu`, seed native-build
path). Distinct locus from the baremetal class
([baremetal_option_field_unwrap_faults_class_2026-07-18](baremetal_option_field_unwrap_faults_class_2026-07-18.md)),
same "Some payload not extracted" family.

## Symptom

```simple
fn main() -> i64:
    val x: i64? = 7
    if val v = x.?:
        return v      # expected 7
    return 0
```

Native-built with the seed on `x86_64-unknown-linux-gnu`, `main()` returns **84**,
not 7. The `if val` **Some-branch is taken** (it does not fall through to
`return 0`), so the Option is correctly recognized as present — but the bound
value `v` is the tagged/boxed `Some` representation, not the unwrapped payload
`7`. i.e. payload extraction after the try-op unwrap is wrong.

## Root cause (bisected)

Introduced by origin commit **`d71449a36dc fix(native): restore canonical Option
ABI`** (first present at base `eb3a695b185`). Evidence:

- The **same** local fix batch produced optnil=**7** at base `874687bc7bf`
  (pre-`d71449a`) and optnil=**84** at base `eb3a695b185` (post-`d71449a`). The
  batch is byte-identical across both bases, so it is ruled out as the cause.
- At `eb3a695b185`, reverting every batch-touched `.?`-lowering-surface file
  (`switch_operators_calls.spl`, `convert_nodes.spl`, `method_calls_literals.spl`)
  to origin-clean leaves optnil=**84** (Stage A + Stage B file-swap tests on the
  already-built seed).
- Origin drift `eb3a695b185..4e8efcf0e53` (28 commits) contains **no `.?` /
  Option-ABI fix** — the regression is still live on current origin.

`d71449a` reworked the Option representation across
`method_calls_literals.spl`, `switch_operators_calls.spl`, `expr_dispatch.spl`,
`function_lowering.spl`, `mir_lowering_stmts.spl`, `core_enum.spl`,
`runtime_native.c`. Origin's own repro
(`native_option_uniform_tagged_abi_repro.spl`) exercises `unwrap_or` and
`through_try` (which *returns* an `Option`), but **not** the
`if val v = x.?: return v` shape that unwraps to a bare payload — that shape is
the blind spot that regressed.

## Root-fix (2026-07-20)

`ExistsCheck` already unwrapped a canonical Option handle through the existing
`option_payload_or_self` owner before the generic runtime-value decoder (the
prior session's partial fix). That alone was verified correct for i64 on a
rebuilt executable (`rc=7`, not `84`) and, it turns out, was ALSO already
sufficient for text/bool via lucky representational accidents (see "Why
text/bool/struct never needed a decode fix" below). Two real defects remained,
found via the sibling-type path-dependence matrix this session ran on a
rebuilt/run native-build executable (not just source text):

### 1. f64/f32 payload encode — FIXED

`ensure_option_handle` (`switch_operators_calls.spl`) passed a float-typed
payload straight into `rt_enum_new`'s i64-declared parameter. The generic
call-argument coercion (`value_as_type` → `select_cast_instruction`) picks
`fptosi` for a double/float → i64 argument — a NUMERIC TRUNCATION (`3.5` →
`3`), not a bit-preserving transfer. The matching decode
(`enum_payload_value`'s F64 arm, same file) does a plain `bitcast` back to
double, so a real `3.5` payload decoded as a denormal near-zero garbage value,
not `3.5`. **Fix:** bitcast float payloads to i64 explicitly in
`ensure_option_handle` before the `rt_enum_new` call, mirroring
`box_runtime_value`'s existing F64/F32 arms (`expr_dispatch.spl`, used for
container/Any-typed float boxing). Verified via `SIMPLE_KEEP_LLVM_IR=1`: the
emitted IR now shows `%l4 = bitcast double %l1 to i64` feeding `rt_enum_new`,
not `fptosi`.

### 2. Struct field-name provenance on ExistsCheck's result — FIXED

`enum_payload_value`'s default arm (non-F64 types) hands back the raw
`ptrtoint`'d payload untouched — correct bits for a struct pointer — but the
merged `result_local` never got a `struct_value_syms`/HIR-type registration.
A later `v.x`/`v.y` field access (`resolve_field_index`) then had neither an
HIR type annotation on `v` nor a `struct_value_syms` entry to consult, and
silently defaulted EVERY field name to index 0 — `if val v = x.?: v.x * 10 +
v.y` on `P(x: 3, y: 4)` returned **33** (both fields read as field 0) instead
of **34**. **Fix:** register the Option's inner struct name onto
`result_local`, preferring `option_inner_hir_type_for_local` (works for the
canonical tagged-handle form) and falling back to
`struct_value_syms.get(base_local.id)` directly for the "raw migration form"
(a struct pointer assigned straight to a `T?` binding — struct construction
itself already registers `struct_value_syms` on that raw pointer, but the
binding never calls `ensure_option_handle` at all: the pointer's own
non-nil-ness already distinguishes Some/None for `rt_is_some`/
`rt_unwrap_or_self`, so the canonical enum-id-1 wrap is skippable and IS
skipped). Verified: `v.x * 10 + v.y` now returns **34**.

### 3. `NullCoalesce` (`??`) shares the same struct gap — FIXED

Cross-lane question (2026-07-20): does `??` share a lowering path with `.?`,
and does either explain a THIRD independent Option-unwrap defect found the
same day (`current ?? mutex_new(0)` on a `Mutex?` in
`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`, reports `== nil` false
but SIGILLs/faults `cr2=0x0` on the first method call — doc
`font_renderer_resolve_metrics_nil_receiver_seed_2026-07-20.md`)? Investigated
directly, not assumed:

- **`.?`/`??` DO share a lowering path — proven, not inferred.**
  `NullCoalesce` (`expr_dispatch.spl`, the case arm immediately above
  `ExistsCheck` in the same file, with an explicit "Mirror the ExistsCheck
  fix" comment already in place) calls the exact same
  `option_payload_or_self` / `decode_runtime_value` / `enum_payload_value`
  helpers. A direct probe confirmed `??` has the IDENTICAL struct
  field-misread symptom `.?` had: `val v = x ?? P(x: 7, y: 8)` returned
  **33** (both fields read as field 0) instead of **42**, on BOTH the
  Some-branch and the None-branch (the `default` expression's own fresh
  construction — an initial same-field-value probe gave a false-negative
  99/99, corrected by re-testing with distinct field values, 77 not 78).
  **Fixed** the same way as `ExistsCheck`: register the merged struct name
  onto `NullCoalesce`'s `result_local` too, trying
  `option_inner_hir_type_for_local` on the left/Option operand, then
  `struct_value_syms` on `left_local`, then `struct_value_syms` on
  `right_local` (the default expression's own construction). Verified both
  branches now return 42/34/78 correctly. See
  `test/03_system/native/option_nullcoalesce_struct*.spl`.

- **This does NOT prove it explains the Mutex/font_renderer crash (#3) —
  evidence points the other way.** Three concrete reasons:
  1. `Mutex` is declared `class Mutex:` (`src/lib/nogc_sync_mut/concurrent/
     mutex.spl:21`), i.e. `SymbolKind.Class`, a DISTINCT enum variant from
     `SymbolKind.Struct` (`src/compiler/20.hir/hir_types.spl:93`). The fix's
     `match ... case Struct:` arm does not fire for a class, in either
     `ExistsCheck` or `NullCoalesce` — an analogous class-provenance gap, if
     one exists, is NOT closed by this fix.
  2. A minimal, isolated class-through-`??`-then-method-call probe on the
     HOSTED path (`class NcC: handle: i64` / `fn get() -> i64: self.handle`,
     `val active = (nil: NcC?) ?? new_ncc(42); active.get()`) returned the
     CORRECT **42** — no crash, no misread — so the struct-provenance gap
     does not obviously generalize to a single-field class on this pipeline.
  3. Most importantly: `_font_mutex_acquire`'s own comment says the fault
     occurs "under freestanding/entry-closure/aggressive-opt **kernel**
     builds" — i.e. the BAREMETAL pipeline, not hosted native-build. This
     bug doc's own header already distinguishes "**HOSTED** native..." from
     the separate `baremetal_option_field_unwrap_faults_class_2026-07-18.md`
     locus ("same family", explicitly NOT the same fix site). Bug #3 is
     baremetal-pipeline; this fix is hosted-pipeline.
  - **Conclusion: adjacent, not proven identical.** Same general symptom
    family (an Option-derived value that looks present but is unusable/wrong
    once actually consumed), but bug #3 most plausibly has its own root in
    the baremetal/kernel codegen path (already root-caused and landed by its
    own lane, commits `b65e09d8eb0`/`e2664d96bdf`, with a documented
    workaround). Do not close bug #3 against this fix.

- **Bug #2** (`text.to_i64() ?? default` + print-interpolation showing
  `n=<value:0x3039>`, doc
  `native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20.md`) is, per that
  doc's own description, a value that is "correctly boxed" but "never
  unboxed for **display**" — i.e. the `??` lowering itself produced a
  correct value; the gap is in the print-interpolation consumer's own
  decode step, a different code path from anything in `expr_dispatch.spl`'s
  `NullCoalesce`/`ExistsCheck` arms. No shared chokepoint found. Adjacent,
  not identical, same conclusion as this doc's existing f64-decode
  cross-reference below.

### Why text/bool/struct never needed a decode fix inside ExistsCheck

`expr_dispatch.spl`'s `ExistsCheck` arm derives its merged result-slot's MIR
type from `expr_value.type_` (the HIR type annotation on the `.?` expression
itself), defaulting to i64 when that annotation is nil. That HIR annotation
turns out to be **unreliable/nil for ALL payload types** here (not just
float) — text/bool/struct/i64 all silently fell back to the i64 default. That
default is harmless for i64 (identity), text/struct (pointer `ptrtoint` /
`inttoptr` round-trips losslessly through an i64 slot), and bool (`trunc`
happens to read the correct low bit for a 0/1 payload) — but NOT for f64/f32,
whose correct round-trip through a raw i64 slot requires a `bitcast`, not the
generic `sitofp`/`fptosi` the backend's argument/copy coercion otherwise
picks for a float↔int type mismatch.

An attempt this session to make `ExistsCheck` derive a type-accurate
`result_type` (mirroring `.unwrap()`'s `option_inner_hir_type_for_local`
pattern) broke text/bool: the OUTER `if val v = x.?:` desugars to a direct
`icmp ne i64 <merge>, 3` sentinel comparison (see the "Bug
(native_i64opt_some0_collapses_to_nil)" comment in `expr_dispatch.spl`), which
is NOT type-aware and requires the merge slot to stay i64/sentinel-comparable
regardless of the real payload type. Forcing `result_type` to `ptr`/`double`
made the None-branch's `emit_const(result_local, Int(3), result_type)` emit
invalid LLVM IR (`add ptr 3, 0` / `add double 3, 0`) and desynced from the
outer sentinel check. **This was reverted** — `ExistsCheck`'s own result slot
must stay i64-uniform; a per-type decode belongs at the consumer, not here.

## f64/f32 decode — SOURCE FIXED (2026-07-22), rebuilt execution pending

With the encode fix landed, the f64 payload's raw bits are now correct
end-to-end through `ExistsCheck`'s i64-uniform slot — but nothing decodes
those bits back to a real `double` before `v` is used in a float context
(e.g. `v == 3.5`). The former repro returned **1** (comparison false) instead
of **42**. `ExistsCheck` now records its inner semantic type on the raw merge
local. `lower_if` keeps the generated `v != nil` sentinel comparison raw, then
temporarily remaps the present-branch binding through `enum_payload_value`.
That existing decoder bitcasts f64 and now reverses the established f32
promotion by bitcasting to f64 before narrowing. The renamed fixture covers
both widths; the already-selected `option_is_none_map` strict dual-backend
case carries the same oracle on Linux, macOS, Windows, and FreeBSD.

Cross-reference: a sibling lane independently found an ADJACENT-but-DIFFERENT
instance in the same general "Option payload value escapes with its tag/raw
representation intact instead of being decoded for its consumer" class:
`native_to_i64_nil_coalesce_print_tagbox_leak_2026-07-20.md` — `text.to_i64()
?? default` feeding print-interpolation shows the CORRECT value but never
unboxed for display (`n=<value:0x3039>`). That is a print-interpolation
consumer gap on `??`; this bug's remaining open half is a float-comparison
consumer gap on `.?`. Both are "a consumer fails to decode-by-type a raw
Option-derived payload", but they are different consumers with no proven
shared chokepoint (no common unbox helper found) — adjacent, not identical
roots. Treat as separate bugs unless/until a shared root is proven.

## Related / class

Same family as the hosted enum-payload box/unbox findings (`a4e7` audit:
`box_enum_payload_if_needed` gates on arg type not declared `Option<T>` element
type; `rt_enum_payload` extract Unbox is shared) and the baremetal Option-unwrap
class. This is a recurring class — see
[feedback_recurring_problem_team_analysis_and_tests] — and needs a codegen
root-fix plus box/unbox + Option-binding regression tests, not a per-shape patch.
The general custom-enum (non-Option) f64 payload encode/decode pair has the
SAME asymmetry and is still open, tracked separately: see
`enum_f64_payload_precision.spl` in `test/03_system/native/README.md`
(`EnumF64Pay.V(0.1)` still returns 40, not 30 — a DIFFERENT construction path,
`lower_enum_construct_named`, not `ensure_option_handle`, so this session's
fix does not cover it).

## Regression coverage

- `test/03_system/native/option_try_unwrap_ifval.spl` (renamed from
  `..._XFAIL.spl`) — i64, expects **7**, now PASS.
- `test/03_system/native/option_try_unwrap_ifval_text.spl` — text, expects
  **42**, PASS.
- `test/03_system/native/option_try_unwrap_ifval_struct.spl` — struct (both
  fields), expects **42**, PASS.
- `test/03_system/native/option_try_unwrap_ifval_none.spl` — None
  short-circuit, expects **42**, PASS.
- `test/03_system/native/option_try_unwrap_ifval_float.spl` — f64/f32,
  expects **42**, source-fixed; rebuilt execution pending.
- `test/03_system/native/option_nullcoalesce_struct.spl` — `??` struct,
  Some-branch, expects **42**, PASS.
- `test/03_system/native/option_nullcoalesce_struct_none.spl` — `??` struct,
  None-branch (default expr), expects **42**, PASS.
- `test/01_unit/compiler/mir/option_variant_order_source_spec.spl` — source
  pins guard float encode/decode, raw sentinel ordering, `.?` struct
  provenance, and `??` struct provenance.

## Repro

`NATIVE_SMOKE_CASES=optnil scripts/check/native-smoke-matrix.shs` (case
`optnil|i64? .? unwrap|...|7`) — was marked xfail against this bug; flip once
this fix redeploys to the smoke-matrix's binary.

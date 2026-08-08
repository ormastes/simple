# JIT array out-of-bounds read leaks the raw `RT_NIL` sentinel (`3`) instead of `nil`/panic

- **Filed:** 2026-08-07
- **Severity:** P2 — wrong text output / missing panic on bare OOB index, no
  crash, no memory-safety issue (`rt_array_get` internally bounds-checks and
  returns cleanly; confirmed 2026-08-07, see Update below)
- **Status:** OPEN — root-caused 2026-08-07, not fixed (Rust-seed defect, see
  Update below)
- **Affects:** JIT/native lane only, confirmed against the currently-deployed
  seed binary (`bin/simple` = Rust seed; self-host Stage-3 blocker still
  open). Both `xs.get(i)` (Option MISS, printed without `??`) and bare
  `xs[i]` (out-of-bounds index) on the same receiver.
- **Found while re-verifying:** `doc/08_tracking/bug/list_get_returns_tag_boxed_value_shifted_left_3_2026-07-28.md`
  (that doc's `<<3` hit-path shift defect is fixed; this is a separate,
  narrower miss-path finding made during that re-verification, split out here
  per the "file it, don't bury it in a closed doc" rule).

## Symptom

```simple
fn main():
    val xs = [10, 20, 30]
    print("miss={xs.get(9)}\n")          # JIT: miss=3   (interpreter: miss=nil)
    print("val={xs[9]}\n")                # JIT: val=3    (rc=0, no panic)
```

`3` is `RT_NIL`, the runtime's flat-Option/OOB sentinel word (see
`dict_get_preserve_flat_nil` and the `emit_const_int(3)` none-arm in
`method_calls_literals.spl`'s `lower_array_first_or_last`, both in
`src/compiler/50.mir/_MirLoweringExpr/`). When the result is consumed through
`??` it is correctly recognized as absent (`xs.get(9) ?? -1` → `-1` on both
engines). When it is interpolated directly into text (no unwrap operator), the
JIT prints the raw sentinel value instead of formatting it as `nil`/`None`,
while the tree-walk interpreter formats it correctly.

## Which engine

| expr | JIT (default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| `xs.get(9)` interpolated bare | `3` — WRONG | `nil` — correct |
| `xs.get(9) ?? -1` | `-1` — correct | `-1` — correct |
| `xs[9]` (bare OOB index, no `.get`) | `3` — WRONG, rc=0, no panic | not re-checked |

Confirmed via `cranelift_jit::backend` log lines that the JIT run was real
(not a silent interpreter fallback). Binary: seed at
`bin/release/x86_64-unknown-linux-gnu/simple` (prints the "bootstrap seed
only" banner); pure-Simple self-hosted lane not re-checked this session (no
bootstrap rebuild performed).

## Root cause (not yet investigated)

Likely: the value's `to_text`/interpolation formatting path decodes/dispatches
on the *declared* element type (e.g. `i64`) without first checking the
Option-nil-sentinel guard that `dict_get_preserve_flat_nil` and the
`Array.first()/.last()` none-arm apply before handing a value to the general
decode/format machinery. Needs someone to trace the interpolation lowering
for a bare Option-typed operand (not wrapped in `??`, `.unwrap()`, or a
`match`) and check whether it takes the same nil-guard branch those call
sites do.

## Not chased further here

Out of scope for the re-verification task that found it; filed so it isn't
lost, not fixed.

## Update 2026-08-07: confirmed live, root-caused, NOT fixed (Rust-seed defect)

### Repro confirmed under the currently-deployed binary

`bin/simple --version` prints the "bootstrap seed only" WARNING banner — the
deployed `bin/simple` **is** the Rust seed (`bootstrap/bootstrap.md`'s known
Stage-3 self-host blocker is still open, so there is currently no alternative
pure-Simple `bin/simple` to test against). Probe:
`/tmp/.../scratchpad/oob_probe.spl` + `oob_probe2.spl` (kept only as evidence
of the exact commands run, not committed).

| expr | seed JIT (default) | seed `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| `xs.get(9)` (miss) interpolated bare | `3` — WRONG | `nil` — correct |
| `xs.get(9) ?? -1` | `-1` — correct | `-1` — correct |
| `xs[9]` (bare OOB index) | `3` — WRONG, rc=0, no panic | `error: semantic: array index out of bounds: index is 9 but length is 3` (panics, rc≠0) |
| `ys[2]` / `ys.get(2)` where `ys=[1,2,3]` (legit value `3`, in bounds) | `3` — correct | `3` — correct |
| `ys.get(2) ?? -1` (legit `3`, in bounds — discriminator) | `3` — correct (NOT replaced) | `3` — correct |
| `ys[-1]` (Python-style wrap, not OOB) | `3` — correct (wraps to last elem) | `3` — correct |

The `ys.get(2) ?? -1` row is the discriminating pair the original doc lacked:
same syntax as the buggy `xs.get(9) ?? -1` row, but here the value is
genuinely present and equals `3`, and `??` correctly leaves it alone on both
engines. This proves the `??` consumer really does check the sentinel bit
pattern (it isn't fooled by legitimate `3`), which narrows the defect to
producer/formatter sites that never look for the sentinel at all — see root
cause below.

### Root cause: this is the Rust seed's OWN MIR lowering, not the `.spl` self-hosted lowering

The seed (`bin/simple` today) does **not** run the pure-Simple compiler's
`src/compiler/50.mir/_MirLoweringExpr/*.spl` at all for its own execution —
it has an independent HIR/MIR lowering + cranelift JIT implemented directly
in `src/compiler_rust/compiler/src/`. Proof: `SIMPLE_MIR_BOUNDS_DEBUG=1
bin/simple run oob_probe.spl` printed **no** `[mir] bounds-check bailout`
line, even though the bailout branch in the `.spl` lowering
(`expr_dispatch.spl:1304-1317`, discussed below) is exactly the kind of path
that would fire for this case if it ran. It never ran, because the seed
binary doesn't execute that source tree.

**Producer defect** — `src/compiler_rust/runtime/src/value/collections.rs:595-611`,
`rt_array_get`:
```rust
pub extern "C" fn rt_array_get(array: RuntimeValue, index: i64) -> RuntimeValue {
    ...
    let idx = normalize_index(index, len);
    if idx < 0 || idx >= len {
        return RuntimeValue::NIL;   // <-- raw sentinel, indistinguishable from a decoded value
    }
    ...
}
```
`RuntimeValue::NIL` = `RuntimeValue::from_special(tags::SPECIAL_NIL)` where
`SPECIAL_NIL = 0`, which encodes to the raw word `3` (matches `RT_NIL` in
`src/runtime/runtime_value.h`). This function performs its own internal
bounds check and returns cleanly on OOB — **there is no out-of-bounds memory
read**; downgrading the "reads raw sentinel" framing from a memory-safety
concern to a silent-wrong-value / missing-panic concern (severity stays P2,
but "leak" should not be read as an OOB memory access).

**Lowering defect (the actual bug)** —
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs:507-523`,
the array-index/`.get()` MIR-emission arm for an array receiver with an
integer index:
```rust
} else if receiver_is_array && matches!(index_ty, TypeId::I8 | ... | TypeId::U64) {
    // HIR already proved this receiver is an array, so avoid the
    // generic collection dispatcher and boxed-index path.
    self.with_func(|func, current_block| {
        let dest = func.new_vreg();
        let block = func.block_mut(current_block).unwrap();
        block.instructions.push(MirInst::Call {
            dest: Some(dest),
            target: CallTarget::from_name(if element_expr_ty == TypeId::STRING {
                "rt_array_get_text"
            } else {
                "rt_array_get"
            }),
            args: vec![receiver_reg, index_reg],
        });
        dest
    })?
}
```
This calls `rt_array_get` **directly, with zero bounds-check emission** (no
call to any `__simple_intrinsic_bounds_check`-equivalent — none exists
anywhere under `src/compiler_rust/compiler/src/codegen`) and **zero
nil-sentinel guard** on the result before it flows into the int-unbox path a
few lines further down (`needs_int_unbox`, ~line 595) that decodes it as a
plain `i64` and hands it straight to text formatting/`print`. There is no
Rust-seed analog anywhere of the `.spl` self-hosted lowering's
`dict_get_preserve_flat_nil` guard (compare-against-3-then-select pattern).
This is why:
- bare `xs[9]` (no `.get`) never panics under the seed's JIT — the seed's own
  lowering never emits any bounds check for array indexing at all, unlike the
  interpreter-mode tree-walker (a *different, independent* Rust
  implementation — `src/compiler_rust/compiler/src/interpreter/expr/collections.rs:523,544,565` —
  which has its own explicit, correct bounds check and panic message).
- `.get(9)` leaks `3` for the same reason: there is no dedicated array
  `.get()` MIR arm at all in the Rust seed (only the generic index path
  above), so `.get()` and bare `[]` indexing are the *same* code path and
  share the same gap.

**Corrected hypothesis vs. the original doc.** The original guess (a
missing nil-check in the *interpolation/`to_text` formatter*) is not the
right frame: the `??` discriminator test above shows some consumer-side code
does correctly test for the sentinel. The actual gap is at the *producer*
side — the MIR lowering for array `get`/index never wraps the value as a
proper flat-Option in the first place (unlike the dict-get path, which does),
so nothing downstream of it has any signal that a nil case occurred.

### Self-hosted `.spl` lane: gap looks structurally similar but could not be dynamically verified

Static inspection of the pure-Simple self-hosted lowering
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl` and
`method_calls_literals.spl`) shows a parallel, but not identical, gap:
- `expr_dispatch.spl:1609` **does** call `emit_bounds_check_for_index` for
  bare `xs[i]`, and that check (when it fires) genuinely panics via
  `__simple_intrinsic_bounds_check` (`runtime.c:1840-1847`, also mirrored in
  `compiler_rust/runtime/src/value/collections.rs:5407-5412`) — so the
  self-hosted lane's bare-index behavior is plausibly *not* affected, except
  for the silent bailout at `expr_dispatch.spl:1304-1317` when no
  `len_symbol` can be resolved for the base type (a narrower, different
  trigger condition than the seed's "never checked at all").
- There is **no dedicated array/list `.get()` lowering arm** anywhere in
  `method_calls_literals.spl` (only dict `.get`, `1216`/`1340`, and
  `.first()`/`.last()`, `3519-3661`, are special-cased with real Option
  wrapping). `xs.get(9)` therefore likely falls through to the same raw
  `rt_array_get` call with no guard, and the interpolation formatter
  (`coerce_concat_operand`, `expr_dispatch.spl:527-610`) dispatches purely on
  declared MIR type with no nil-sentinel branch — so `.get()` misses plausibly
  leak `3` on the self-hosted lane too.

This could **not** be dynamically confirmed: `bootstrap/stage3/simple
native-build` currently segfaults even on a trivial `print("hello\n")`
program (rc=139, core dump, no useful diagnostic beyond
`[mir-lower-expr]`/`[mir-method-call]` trace spam) — this matches the
already-tracked, unrelated Stage-3 self-host blocker in
`.claude/rules/bootstrap.md` / `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`
family (see also memory note "Stage-3 hello-world SEGV = BORROW CHECKER
field-index collision"). No `.spl`-lane fix was attempted blind without a
working binary to verify it against.

### Disposition: confirmed live, NOT fixed

- **Status:** OPEN (unchanged), reclassified as root-caused.
- **Why not fixed:** the reproducible, root-caused defect lives entirely in
  the Rust seed's own MIR lowering
  (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs`), which
  is out of scope for a "small, contained `.spl` fix" — it's compiled Rust
  behind the seed/bootstrap machinery, changing it risks destabilizing the
  bootstrap chain, and per project policy the seed is bootstrap-only (fixes
  belong in pure-Simple where possible). The parallel `.spl`-lane gap
  (missing array `.get()` Option-wrapping arm, no nil guard in
  `coerce_concat_operand`) is a plausible, separately-fixable `.spl` issue,
  but is currently unverifiable end-to-end because `bootstrap/stage3/simple
  native-build` is independently broken (segfaults on hello-world).
- **No regression spec added.** Per project convention, a spec asserting the
  correct (nil/panic) behavior would land red with no fix behind it, and
  CLAUDE.md forbids landing new failing tests without approval. Deferred
  until either (a) the Rust-seed lowering gets a bounds-check + nil-guard fix,
  or (b) the Stage-3 SEGV blocker clears enough to verify a `.spl`-lane fix
  for the array `.get()` arm.

### Suggested fix shape (for whoever picks this up)

1. Rust seed (`lowering_expr_struct.rs` array-index arm): emit a
   bounds-check call before `rt_array_get`/`rt_array_get_text` for bare
   index-on-array (matching the panic semantics the tree-walk interpreter
   already has), and for `.get()` specifically, wrap the result as a real
   tagged Option (or apply a compare-against-`RuntimeValue::NIL`-then-select
   guard mirroring the dict-get pattern) before any unboxing/formatting.
2. `.spl` self-hosted lane: add an array/list `.get()` MIR arm mirroring
   `lower_array_first_or_last`'s Option-construction pattern instead of
   falling through to raw `rt_array_get`, and add an `RT_NIL`-guard to
   `coerce_concat_operand` (and `lower_bootstrap_print_call`) for
   Option-typed locals, reusing the `dict_get_preserve_flat_nil` compare/select
   pattern (`expr_dispatch.spl:895-946`) — verify only once Stage-3
   native-build stops segfaulting on trivial programs.

## 2026-08-08 re-verification — STILL LIVE, fence added

**Binary**: deployed `bin/simple` (`bin/release/x86_64-unknown-linux-gnu/simple`,
mtime 2026-08-08 00:53, seed banner confirmed via `--version`) — the Rust
seed, same binary this bug's root cause lives in. Fixture:
`test/fixtures/jit_array_oob_nil_sentinel/main.spl` (kept in-tree, unlike the
prior session's scratch-only probes, so a fence can drive it).

| expr | JIT (default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| `xs.get(9)` (miss, OOB) | `3` — WRONG | `nil` — correct |
| `ys.get(2)` / `ys[2]` (legit value `3`, in bounds — discriminator) | `3` — correct | `3` — correct |
| bare `xs[9]` (OOB) | `3`, rc=0, no panic — WRONG | panics `array index out of bounds: index is 9 but length is 3`, rc=1 — correct |

Confirmed real JIT engagement (not silent interpreter fallback) via
`RUST_LOG=cranelift_jit=debug`: `cranelift_jit::backend: defining function
funcid58: function u0:58() -> i32 system_v` printed for this exact probe.

**Divergence from the 2026-08-07 record, noted but not chased**: that
session's `ys.get(2) ?? -1` discriminator row claimed `-1` — correct
(NOT replaced)`. Re-run today on the same expression (`val v = ys.get(2) ??
-1` and inline, both forms, 3x repeat, deterministic) instead prints `-1` on
JIT (`interpret` still correctly prints `3`) — i.e. the `??` operator itself
now appears to coalesce the genuine in-bounds value `3` away, treating it as
if it were the nil sentinel. This is either a regression introduced by
whatever produced today's binary (rebuilt 2026-08-08 00:53, after
yesterday's finding) or a mismeasurement in the prior session — not
re-investigated here, out of scope for this pass. The fence below therefore
does NOT rely on `??` as a discriminator; it uses cross-engine comparison of
a genuine in-bounds `3` (`ys[2]`/`ys.get(2)`, bare interpolation, no `??`)
instead, which reproduced identically to the 2026-08-07 record and is stable
across repeats.

**Fence**: `scripts/check/check-jit-array-oob-nil-sentinel.shs`, modelled on
`check-native-tuple-to-text.shs` / `check-native-object-cache-granularity.shs`
(adapted for `bin/simple run` + `SIMPLE_EXECUTION_MODE=interpret` instead of
`native-build`, since this is a JIT/interpreter divergence, not an AOT one).
Hard-asserts the interpreter's correct behaviour (miss=nil, in-bounds
control=3/3, bare OOB panics with the exact message and nonzero rc) as a
prerequisite gate, then records the JIT's current wrong behaviour as
`KNOWN-OPEN` (exit 0) with the expected-correct values stated inline; flips
to `FAIL (promote-me)` if the JIT lane ever starts matching the interpreter,
and to a plain `FAIL` if the JIT in-bounds control itself regresses
(distinguishing "this bug fixed" from "something else broke").
Sabotage-verified: corrupting the fixture's in-bounds control value
(`ys=[1,2,3]` → `[1,2,4]`) makes the script print `FAIL — interpreter lane
control regressed` and exit 1; restoring the fixture (verified byte-identical
via `diff`) makes it pass again (`KNOWN-OPEN`, exit 0).

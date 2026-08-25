# `Poll.unwrap` steals `.unwrap()` in `lower_and_check_impl` — a SECOND, independent bind site

- **Filed:** 2026-08-25
- **Status:** **FIXED and MEASURED 2026-08-25.** The 4 call sites are gone
  (4 → 0, by disassembly) and the `E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED`
  signature is ABSENT. The gate's *symbolic* check is green. Its *behavioural*
  check is still red: hello world on Stage 2 now SEGVs **much later**, in
  `native_compile` (step 5/6), from a **different, previously-unreachable**
  cause — filed separately as
  `stage2_native_compile_segv_after_unwrap_fix_2026-08-25.md`. The gate therefore
  stays ADVISORY red, with its red re-attributed.
- **Severity:** blocks the Stage-2/Stage-3 self-host lane (rc=139 on hello world).
- **Parent record:** `stage3_n_modules_zero_segv_mir_lowering_x86_64_2026-08-24.md`
- **Gate:** `scripts/check/check-stage2-option-unwrap-not-stolen.shs` (ADVISORY, honestly RED — red *because of this bug*)

## What this is, and what it is NOT

`.unwrap()` on an Option whose receiver type is erased is bound to
`lib__nogc_async_mut__async__poll__Poll_dot_unwrap`. `Poll.unwrap` tests the
`Poll::Ready`/`Poll::Pending` discriminants, matches neither `Some` tag, falls
through and returns 0. Zero is `< 4096`, so `rt_heap_ref_wellformed` reports the
payload malformed while the field still holds a real enum — hence
`E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED` and the rc=139 self-host death.

That much is the parent record's defect. **What is new here is that there are
TWO independent bind sites producing it, and only one has been fixed.**

**This is NOT the name-suffix single-candidate tail** in
`compile_method_call_static` (`codegen/instr/closures_structs.rs`). That site
was found, fixed, measured, and landed on 2026-08-25. Do not re-investigate it;
that is a solved path and re-litigating it has already cost this defect several
lanes.

## The measurement that isolates this site

Per-function callee counts by disassembly, pre-fix vs post-fix Stage 2, both
built from base `4d11699bc5b` by the same replayed bootstrap argv (cranelift,
full `src/compiler` + `src/app` + `src/lib` closure):

| function | `Poll_dot_unwrap` | `rt_unwrap_or_trap` |
|---|---|---|
| `run_named_pass_with_record` | 3 → **1** | 0 → **2** |
| `run_pass_on_module_checked` | 3 → **1** | 0 → **2** |
| **`lower_and_check_impl`** | **4 → 4** | **0 → 0** |
| whole binary | 307 → **272** (−35) | 117 → **151** (+34) |

Read this carefully, because it is the whole case:

- The suffix-binder fix works. `rt_unwrap_or_trap` gains exactly **+34**, and
  the sites moved in precisely the functions the original codegen probe named.
  (The whole-binary `Poll_dot_unwrap` delta reads −35 rather than −34 because
  of one further reference in the unrelated `DimSolver_dot_solve_constraint`
  that differs between two builds of the same fix — build variance, not this
  fix. The per-function rows are identical across both builds.)
- `lower_and_check_impl` did not move **at all** — not one of its 4 sites, and
  it gained zero builtin calls. A fix that genuinely covered this path could
  not leave it bit-for-bit unchanged.
- Therefore these 4 sites are reached by a **different mechanism**.

All 4 surviving sites target the same wrong symbol:

```
objdump -d <post-fix stage2>  # within lower_and_check_impl
  4 x <lib__nogc_async_mut__async__poll__Poll_dot_unwrap>
```

## Corroborating negative evidence

- The erased-receiver codegen probe (`SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1`)
  reports **zero** `unwrap` suffix binds on the fixed compiler, and zero
  occurrences of the string `Poll_dot_unwrap` anywhere in its output — while
  remaining demonstrably live (64 bind lines across 12+ other methods:
  `with_note`, `build`, `map`, `kind`, `lower_const`, `add_port`, …). So this
  site does not announce itself through that reporter at all.
- The `calls.rs` import-ladder / `imports.rs` ambiguous-first-wins hypothesis is
  **refuted, twice, by instrumentation on real self-host builds**. Across a full
  compile the ladder probe fired exactly twice, both for the unrelated
  `expr_force_unwrap` via `use_map_direct`. Do not restart there.

## Why no fixture will reproduce this

`func_ids` is per-module. A small single-module build never has `Poll.unwrap` in
scope, so the decoy that makes the theft possible does not exist. Every attempt
to shrink this to a fixture has failed for that reason. Reproduction requires a
real Stage-2 self-host compile (~10 min on a warm cache) via the replayed
bootstrap argv — the bootstrap scrubs `SIMPLE_DEBUG_*`, so instrumenting it
requires replaying its argv rather than invoking it.

## MECHANISM (located 2026-08-25)

It is the **cross-module resolution ladder** in `compile_method_call_static`
(`codegen/instr/closures_structs.rs`) — the `func_id == None` branch, reached
*because* the first fix now returns `None`. Four steps:

```
1. ctx.use_map.get(func_name)                  -- BARE name, direct hit
2. scan use_map    for a key ending ".{name}"  -- first-wins, `break`
3. scan import_map for a key ending ".{name}"  -- first-wins, `break`
4. ctx.import_map.get(lookup_name)             -- BARE name fallback
```

**Only step 4 carried the Option/Result-family exclusion.** Steps 1–3 ran first
and were unguarded. `imports.rs` inserts **bare raw method names** into
`use_map`, and in the self-host closure the only library defining an `unwrap`
method is `nogc_async_mut/async/poll.spl` — so step 1 hit
`use_map["unwrap"] -> lib__nogc_async_mut__async__poll__Poll_dot_unwrap` and
never reached the exclusion sitting below it.

`T?` is the reason the receiver is erased: it lowers to `HirType::Pointer`,
which has **no registered type name**, so `mir/lower` emits
`MethodCallStatic { func_name: "unwrap" }` with no qualifier.

### Why the 4 → 4 differential looked like "untouched"

This is the part the handoff got wrong, and it is worth stating plainly. The
first fix **did** change this function's resolution path: those 4 calls stopped
being bound by the suffix binder and were *immediately re-stolen* by step 1 of
this ladder — onto the **same wrong symbol**. An unchanged count masked a
changed path. "A fix that genuinely covered this path could not leave it
bit-for-bit unchanged" was a reasonable inference and a false one: two distinct
binders selecting one symbol are indistinguishable by callee count alone.

### Latent flake, fixed at the same time

Steps 2 and 3 take the **first** match out of a `HashMap` iteration, which is
nondeterministic. Leaving them unguarded is a latent flake even when step 1
misses — plausibly the source of the unexplained one-site build variance in
`DimSolver_dot_solve_constraint` recorded in the parent commit message.

## Fix

All four steps now skip an unqualified Option/Result-family name. Skipping is a
**route, not a refusal**: `None` falls through to
`try_compile_builtin_method_call`, which lowers the call to the runtime enum
builtins and declares the symbol on demand, so no raw name survives to link (this cannot
regress into the NULL-GOT class that produces the same rc=139 by another cause).
Qualified spellings are unaffected — `lookup_name` is `func_name` with `_dot_`
rewritten to `.`, so matching a bare spelling exactly implies no type qualifier.

Gate: `scripts/check/check-cross-module-ladder-family-not-name-bound.shs`,
mutation-tested both directions against real source (PASS on the fixed tree,
FAIL on real `origin/main` content). Deliberately a **sibling** of
`check-erased-receiver-family-not-suffix-bound.shs`, not an edit to it: that
gate's fixture 5 asserts the cross-module exclusion is *not* the guard it pins.

## Further dead ends closed by reading the code (do not restart here)

- `mangle.rs`'s `resolve_call_target` (587) and `resolve_method_call_static`
  (722) **already carry** this exclusion — and both are reached only from
  `mangle_mir`, whose single non-test caller sits inside **both** `if use_llvm`
  and `#[cfg(feature = "llvm")]` (`native_project/compiler.rs:837-849`). Inert
  on the cranelift reproducer, confirming the handoff's dead-end call
  independently.
- `resolve_defined_suffix_alias` (`stubs.rs:371`) probes suffix `"__unwrap"`,
  which `..._Poll_dot_unwrap` does not end with, and is uniqueness-guarded.
- **No fixture reproduces it — re-confirmed, with the attempt recorded.** A
  two-shape fixture covering both real receiver spellings (nested field chain
  `outer.ctx.surfaces.unwrap()`, and a locally-annotated `T?` from an
  if-expression) built and ran **correctly**, with zero `Poll_dot_unwrap` in the
  binary. The per-module `func_ids` argument holds; the stdlib's `Poll` is not
  pulled into a small closure. A real Stage-2 compile remains the only proof.

## Suggested next step

Instrument the resolution of a bare `unwrap` **outside** the suffix binder —
i.e. whatever path `lower_and_check_impl` actually takes — and bisect on which
call in that function produces the `lea`/indirect-call pair. Note
`grep -c "call.*Poll_dot_unwrap"` returns 0 on a binary calling it hundreds of
times (it is `lea` + indirect); use symbol-aware disassembly.

## Reproduce

```sh
sh scripts/check/check-stage2-option-unwrap-not-stolen.shs --stage2 <stage2-binary>
# expect: FAIL -- ... 4 Simple '*_dot_unwrap' call site(s) inside lower_and_check_impl ...
```


## Measurement (Stage 2, base `c6041e04d4e` + this fix)

Base probed clean BEFORE measuring, per the native-build poisoning hazard:
hello world on the seed `HW_BUILD_RC=0`, `HW_RUN_RC=0`; re-probed on the fixed
seed `HW2_BUILD_RC=0`, `HW2_RUN_RC=0`.

Stage 2 built by the sanctioned invocation
(`bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2`):
**757 compiled, 0 failed**, linked. Rejected at sanity (see below), binary
preserved as `stage2/x86_64-unknown-linux-gnu/simple.rejected` and measured there.

Per-function, by symbol-aware disassembly (`objdump --disassemble=<sym>`):

| function | `Poll_dot_unwrap` | observed replacement |
|---|---|---|
| `lower_and_check_impl` | **4 → 0** | `rt_enum_payload` ×6 |
| `run_named_pass_with_record` | 1 → 0 | — |
| `run_pass_on_module_checked` | 1 → 0 | — |
| whole binary | 272 → **0** | `rt_enum_payload` ×8431 |

**The callee is `rt_enum_payload`, not `rt_unwrap_or_trap`** (whole-binary
`rt_unwrap_or_trap` = 8). Both are named as correct Option builtins by the gate's
own header. This is stated as *observed*; the parent record was rewritten twice
for claiming intent as measurement, and this row is the objdump result.

Gate verdict changed, and the change is the point:

```
before: FAIL -- 2 check(s) performed: 4 Simple '*_dot_unwrap' call site(s)
        inside lower_and_check_impl ...; hello world emitted
        E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED (rc=139)
after:  FAIL -- 2 check(s) performed: hello world crashed the
        Stage-2 compiler (rc=139)
```

The call-site clause and the malformed-signature clause are both **gone**;
measured by hand, `E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED` count = **0**.

### Why whole-binary 0 is the correct result, not an over-broad guard

`Poll_dot_unwrap` is no longer even DEFINED in the binary (`nm` count 0), and
zero `*_dot_unwrap` symbols survive anywhere. That looks alarming and is not:
the tree contains **zero qualified `Poll.unwrap` call sites** (the only
`future.poll().unwrap()` is inside a docstring example in
`nogc_async_mut/async/promise.spl:20`). Every one of the 272 references was a
theft; with the thefts removed the method has no callers and is
dead-code-eliminated.

**Honest limit:** because no genuine qualified caller exists in the closure, this
build **cannot demonstrate** that qualified resolution still works. That claim
rests on code reading — `lookup_name` is `func_name` with `_dot_` rewritten to
`.`, so an exact match on a bare spelling implies no type qualifier — not on
measurement.

### What is NOT fixed

Hello world still SEGVs, now at `native_compile` step 5/6, **after**
`borrow_check`, `process_async`, `optimize_mir`, `weave_aop` and `native_cache`
all complete. No pre-fix build ever reached that phase — the earlier crash masked
everything downstream — so this is a **newly-exposed** defect, not a
pre-existing one, and "regresses nothing" would be the wrong phrasing.

`--entry` vs positional (lane-s7's discriminator) was **not** reproduced here:
the `--entry` run was reaped with no `.rc`, which per the attribution harness is
UNKNOWN, never a pass. Recorded as unmeasured rather than inferred.

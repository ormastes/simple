# FIX IMPLEMENTED, STAGE 4 REVALIDATION PENDING: staged-native SSA rewrite loses definitions and stores

- **Date:** 2026-08-01
- **Status:** SECOND ROOT CAUSE FOUND AND FIXED 2026-08-17 (see the section at
  the bottom). Stage 4 revalidation still pending.
- **Correction to the 2026-08-03 entry below:** the claim "the focused native
  oracle passes" was **not true at HEAD**. Re-run 2026-08-17, the oracle
  `test/01_unit/compiler/mir_opt/ssa_alloca_store_retention_native_check.spl`
  failed (`rc=1`, `FAIL: alloca rewrite dropped a defining instruction or its
  slot store`). The 2026-08-03 named-record change is real and is retained, but
  it was **inert**: the transform it repairs was never reached for the
  functions in question. Do not read the 2026-08-03 section as a closed fix.
- **Related:** `llvm_bootstrap_ir_buffer_not_reset_2026-08-01.md` (the sibling
  "corrupt target triple" defect, FIXED — it was a *different* bug).

## Claim under investigation

The pure-Simple LLVM backend emits functions whose bodies are lost: every
function comes out as `ret i64 0`, and under `-O3` the whole body folds away.

## Result: the LLVM text-emission layer is NOT the cause (PROVED)

Every emission site that could plausibly drop a constant was driven directly
and emitted **correctly**. Harnesses were run against the real compiler
modules (not mirrors), with `SIMPLE_BOOTSTRAP=1`.

### 1. `MirToLlvm.translate_const` — CORRECT

Driving the real `translate_const` with real `MirConstValue`s:

```
  %l0 = add i64 42, 0  ; const int
  %l1 = add i64 7, 0  ; const int
  %l2 = add i64 1, 0  ; const bool
  %l3 = add i64 0, 0  ; const zero
```

`Int(42)` and `Int(7)` survive. The enum match over `MirConstValue` dispatches
to the right arm — it does **not** fall through to the `Zero` arm (which was the
leading hypothesis, since `Zero` emits `add {ty} 0, 0` and would produce exactly
the reported symptom).

### 2. `MirToLlvm.translate_terminator` (`Ret`) — CORRECT, both paths

```
  ret i64 42                      # Path A: Ret(Some(Const Int 42))
  %l0 = add i64 99, 0  ; const int
  ret i64 %l0                     # Path B: Ret(Some(Copy(local)))
```

This clears the "return a defined zero" fallback at `core_codegen.spl:821`
(`return_locals.has(...) or not local_types.has(...) or not
defined_locals.has(...)` → `emit_ret(..., "0")`). That branch is a strong
structural candidate — if any of those three dict lookups misbehaved, *every*
function would return 0 — but it did **not** fire for a normally-defined local.

### 3. `LlvmIRBuilder.emit_ret` / module header — CORRECT

`emit_ret("i64", "42")` produced `ret i64 42` verbatim, and the emitted module
passed `llc-18 -filetype=obj` (rc=0, object with symbol `T mod_b`).

## Engine caveat — the axis NOT yet covered

All three probes above executed under the **tree-walking interpreter**. They
were launched as a bare positional `.spl` (which selects the JIT), but the JIT
declined the module and fell back:

```
[jit-fallback] unresolved external symbol 'LlvmIRBuilder_dot_create':
whole module dropped to the interpreter (expect ~100-1000x slowdown).
```

So the correct reading is: **the backend logic is right, and the interpreter
executes it right.** It is still open whether JIT or native codegen miscompiles
these same functions. That matters, because the deployed compiler runs this code
as **native** code, and there is a documented pattern in this repo of JIT+native
being silently wrong where the interpreter is correct.

An attempt to compile the probe natively for that comparison failed early on
import resolution, not on the defect:

```
error: semantic: Undefined("undefined identifier: MirToLlvm")
```

(`simple compile --native` does not resolve compiler-internal modules the way
the run path does.) A different vehicle is needed to get these functions under
native codegen.

## Remaining hypothesis space (in suggested order)

1. **Native/JIT miscompilation of the backend itself.** Get `translate_const` /
   `translate_terminator` executing under native codegen and re-run the exact
   probes above. Highest prior, given the interpreter/native divergence history.
2. **The MIR never contains the constants.** In the bootstrap real-LLVM path the
   MIR is not built in Simple — it is pulled through the extern bridge
   (`bootstrap_mir_function_at(idx)` etc., `driver_bootstrap.spl:391+`), i.e. it
   comes from the Rust seed. If those externs hand back empty/zeroed bodies, the
   backend would faithfully emit `ret 0` and everything above would still be
   correct. Note an unregistered `@extern fn` returns nil **silently** in this
   repo. Probe the bridge's output before blaming codegen.
3. Constant folding / MIR opt upstream of the backend.

## 2026-08-03 root-cause update: heterogeneous tuple transport in the alloca rewrite

The preserved flat-bootstrap IR narrowed the loss to
`ssa_alloca_transform_blocks`, not constant construction or LLVM text emission.
`lib.nogc_async_mut.env.platform.detect_os` contained 27 generated `alloca`
instructions and 26 read-side `load` instructions, but zero `store`
instructions and zero defining constants. This asymmetric shape matters:
`ssa_alloca_rewrite_inst_operands` was still returning its prepended loads, while
the nested tuple returned through `ssa_alloca_apply_def_store` and
`ssa_alloca_rewrite_inst` lost the core `MirInst` and appended `[MirInst]`
fields under staged-native execution.

The exact hard-exit oracle constructs a cross-block-live boolean definition;
the adjacent case uses a text-pointer constant. Both require this complete
sequence to survive: entry `Alloc`, renamed `Const`, `Store`; successor `Load`;
`Ret` of the loaded local. The same oracle compiled natively by the Rust seed
passed before the fix, proving the transform algorithm itself was sound and
isolating the divergence to pure-Simple staged-native value transport.

The pure-Simple fix replaces the two heterogeneous anonymous tuple results with
named `SsaAllocaDefStoreResult` and `SsaAllocaRewriteInstResult` records. The
block rewrite consumes named fields, so a core definition and its store travel
as one typed value-flow unit. No LLVM legalization or source-level fallback is
used; legalizing the later `i1 -> ptr` symptom alone would have masked an
uninitialized slot and returned address zero or one as text.

Regression: `test/01_unit/compiler/mir_opt/ssa_alloca_store_retention_native_check.spl`.

## Not the cause (checked, ruled out)

- **`LlvmTargetTriple.to_text()`** — returns `x86_64-unknown-linux-gnu` and
  `x86_64-unknown-simpleos` correctly for the `Some(env)` / `nil` cases.
- **The bootstrap IR buffer leak** — real, fixed separately, but it duplicates
  module headers; it does not zero function bodies.
- **`run_effect_pass`** (`src/compiler/30.types/type_system/effect_pass.spl:27`)
  — evaluated and **does not bear on this defect**. Correcting the record: this
  is *not* a guard that fails to skip the pass. It is an **unconditional early
  `return (modules, empty_warnings)`** at the top of the function, with no env
  check anywhere, so the effect pass **never runs on any build** and its entire
  body — docstring and all 5 documented steps — is dead code. (The earlier
  description, "the guard has never worked so the pass runs on every build", is
  exactly backwards.) Effect inference only annotates `HirFunction.effects`
  for purity/readonly attributes; it does not participate in constant lowering
  or return-value emission. Left unchanged, as it is a separate latent issue
  and stage2 is green with it as-is.

## 2026-08-17 second root cause: the alloca lane never ran on value-returning functions

Reproduce-first. The oracle was RED at HEAD despite the 2026-08-03 fix being
present in source (`SsaAllocaDefStoreResult` /`SsaAllocaRewriteInstResult` are
at `var_reassign_ssa.spl:32,42`):

```
$ bin/simple run test/01_unit/compiler/mir_opt/ssa_alloca_store_retention_native_check.spl
FAIL: alloca rewrite dropped a defining instruction or its slot store   # rc=1
```

Instrumenting `ssa_alloca_transform_blocks` to print its reject reason showed the
transform was not dropping anything — **it was never applying**:

```
bool applied=false reason=unsupported value return terminator
text applied=false reason=unsupported value return terminator
```

### One bug, three sites, all in `src/compiler/60.mir_opt/mir_opt/var_reassign_ssa.spl`

Each site independently assumed the `Ret(Some(...))` payload must never be
inspected, and each therefore skipped it:

1. **Admission** (`ssa_alloca_transform_blocks`, was line 1645) rejected any
   function containing a value-returning terminator:
   `if ssa_term_has_value_return(...): reject("unsupported value return terminator")`.
   Since virtually every non-void function ends in `Ret(Some(...))`, the alloca
   lane was disabled for **the entire population it exists to serve**. This is
   why the 2026-08-03 named-record fix changed nothing observable.
2. **Liveness** (`ssa_collect_term_operand_locals`, was line 1296) treated `Ret`
   as contributing no uses. A local defined in one block and returned from
   another has its *only* use in that terminator, so it never entered the
   cross-block-live set. With site 1 fixed alone the reject merely moved to
   `reason=no slotted locals` — proving both sites are load-bearing.
3. **Rewrite** (`ssa_alloca_rewrite_term`, was line 1580) returned the
   terminator untouched, commented "Admission rejects Ret(Some(...))". Had
   sites 1 and 2 been fixed without this one, a slotted local would have been
   returned *without being loaded back out of its slot* — a use with no
   reaching def, i.e. the reported `ret i64 0` symptom, now caused by the fix.

The three comments referenced each other's assumption, which is why the gap
survived: each site looked locally justified.

### Fix

Added `ssa_ret_payload_operand(term)`, which returns the returned operand or nil
and is guarded by the existing presence check. All three sites now use it:
liveness counts the returned operand as a use; `ssa_term_operand_payloads_valid`
validates it via `ssa_operand_local_payload_valid` instead of `case Ret(_): true`;
and the rewrite loads a slotted local before the `Ret` reads it. The
staged-native transport safety is **preserved, not removed** — an undecodable
payload still rejects the function, via the payload check rather than a blanket
kind check, so the failure mode degrades to "not slotted", never to a wrong
rewrite.

After:

```
$ bin/simple run test/01_unit/compiler/mir_opt/ssa_alloca_store_retention_native_check.spl
PASS: alloca rewrite retains bool and text-pointer definitions and stores   # rc=0
```

### Regressions added

- `test/01_unit/compiler/mir_opt/ssa_alloca_value_return_slotting_spec.spl` —
  reproducer, one `it` per gate so a partial regression is distinguishable.
- `test/01_unit/compiler/mir_opt/ssa_alloca_terminator_use_coverage_spec.spl` —
  detection spec for the class: asserts every operand-carrying terminator kind
  (`Ret`/`If`/`Switch`) is wired into all three of liveness, validation and
  rewrite, plus the invariant that no terminator still names a slotted local
  after the transform. A new terminator kind added without wiring fails here.

Note the existing oracle is a top-level script, not a spec: `bin/simple test` on
it reports `zero-examples` and `Results: 1 total, 0 passed, 1 failed` regardless
of the assertion. It must be run with `bin/simple run`. The two specs above
replace it as the gate.

### NOT proved

Stage 4 revalidation is still outstanding, and is now **more** important, not
less: this change makes the alloca transform newly run on nearly every
value-returning function in the bootstrap LLVM path, which is a large behaviour
change that no interpreted spec can cover. A bootstrap owner must rebuild
Stage 3 and repeat the failed shard before this is CLOSED.

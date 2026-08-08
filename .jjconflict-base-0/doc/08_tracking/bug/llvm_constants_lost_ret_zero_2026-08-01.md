# FIX IMPLEMENTED, STAGE 4 REVALIDATION PENDING: staged-native SSA rewrite loses definitions and stores

- **Date:** 2026-08-01
- **Status:** PURE-SIMPLE ROOT FIX IMPLEMENTED 2026-08-03; the focused native
  oracle passes, but the x86 Stage 4 owner must rebuild the pure-Simple Stage 3
  compiler and repeat the failed shard before this becomes CLOSED.
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

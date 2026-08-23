# Codegen fails OPEN: an unlowered MIR kind ships a linked binary that panics at run time

- **Date:** 2026-08-23
- **Status:** FIXED (fail-open closed); the 33 unlowered kinds themselves remain unimplemented, now named loudly
- **Severity:** CRITICAL — "the build says success and the program is wrong"
- **Area:** `src/compiler/70.backend/backend/_MirToLlvm/`, `src/compiler/70.backend/backend/_CBackendTranslate/`

## Symptom

An ordinary program using `Result<i64, text>` and the `?` propagation operator
builds with **rc=0**, reports **step 6/6**, and links. Running the produced
binary:

```
PANIC: E-BACKEND-LLVM-INST-ResultMatchSemantic: LLVM backend does not lower ResultMatchSemantic
```

Reproduced live on this tree (fixture in
`scripts/check/check-codegen-unlowered-mir-fails-build.shs`).

## Mechanism

`MirToLlvm._unsupported_llvm_inst` (core_codegen.spl) routes 33 `MirInstKind`
variants with no LLVM arm into `MirToLlvm.emit_unsupported_panic`
(`_MirToLlvm/asm_constraints_helpers.spl`). That helper emitted a
`call void @rt_panic(...)` + `unreachable` **into the generated IR** and
returned normally. Codegen therefore *succeeded*, the module linked, and the
defect became a **runtime** failure of the shipped artifact.

Lane C7 (2026-08-21) had already fixed the worse ancestor of this — those 33
variants used to be *silently dropped* by a shared `case _: ()` — by giving each
a named `E-BACKEND-LLVM-INST-<Variant>` code. What C7 did not change is *when*
the failure lands: it stayed at run time.

The C/C++ backend carried the identical twin: `CBackendTranslate.emit_unsupported_panic`
(`_CBackendTranslate/class_core.spl`) emitted `spl_panic("...")` into the
generated C, ~40 call sites, same fail-open shape.

The full unlowered set (33) is: ConditionProbe, Drop (deliberate no-op),
HostGpuLaneBegin/End, MaskFromCmp, MaskedAdd/Fma/Mul, MirSimd{Binop,Cmp,Gather,
Load,MaskOp,Permute,Reduce,ScalableVsetvl,Scatter,Select,Shuffle,Splat,Store,
Ternop,Unop}, MirWarp{ActivesMask,Ballot,Reduce,Shfl,Sync}, Predicated{Add,Fma,
Mul}, **ResultMatchSemantic**, ScalableVecFence. Only `ResultMatchSemantic` is
general-purpose and on the stage1 path; the other 30 are SIMD/GPU.

## Fix

`emit_unsupported_panic` now raises a **compile error** naming the kind and the
site, in both backends. This matches the treatment `DecisionProbe` /
`ConditionProbe` already had in `core_codegen.spl`, which panicked at COMPILE
time. `SIMPLE_ALLOW_UNLOWERED_MIR=1` restores the old emit-and-hope behaviour
for anyone deliberately exercising the runtime-panic path.

Verified: the same fixture that previously linked green now stops the build with

```
error: E-BACKEND-LLVM-INST-ResultMatchSemantic: LLVM backend does not lower ResultMatchSemantic at unknown location
error: native-build worker exited with code 1.
```

## Known limits, stated rather than papered over

- The span is `unknown location` on this fixture: the `MirInst.span` for
  `ResultMatchSemantic` is empty. The diagnostic still names the kind, which is
  what makes it actionable; improving span propagation is separate work.
- This closes the fail-open. It does **not** implement any of the 33 kinds.
  `Result` + `?` therefore now fails the build loudly where it previously
  shipped a dead binary — a strictly better failure, but still a failure, and
  `ResultMatchSemantic` needs a real LLVM arm before stage1 can build.

## Gate

`sh scripts/check/check-codegen-unlowered-mir-fails-build.shs` — builds the
`Result` + `?` fixture and fails if the build reports rc=0 while the binary
dies at run time, or if a failing build emits no named
`E-BACKEND-LLVM-INST-*` diagnostic. Fatal `--selftest`-equivalent runs first.
`0 fixtures built`, a missing compiler, or a timed-out build are all ERROR
(exit 2), never a pass.

## Class sweep — 7 MORE fail-open backends, FILED not fixed here

The same mechanism exists in seven other backends. They are listed with exact
sites so a follow-up lane can close them; they are deliberately NOT changed in
this commit, because a hard failure on the Cranelift/JIT path could surface
real breakage in lanes this change has not exercised, and correctness beats
speed.

**(a) SILENT — instruction dropped, no diagnostic at all (worst):**

| # | site | note |
|---|---|---|
| 1 | `70.backend/backend/cranelift_codegen_adapter.spl:761` `cl_translate_instruction` | `case _: ()`, comment says "skip silently for now". JIT/AOT path. Widest blast radius. |
| 2 | `70.backend/backend/common/mir_text_codegen.spl:289` `translate_unsupported`, dispatched from `case _:` at :180 | BASE trait for the text backends — every subclass that does not override inherits the fail-open. |
| 3 | `70.backend/backend/llvm_lib_translate_expr.spl:225` `translate_instruction` | inkwell/llvm-lib backend; print-only warning, then continues. |
| 5 | `70.backend/backend/wasm/wat_codegen.spl:393` `translate_instruction` | emits `;; unhandled instruction`, a WAT comment = a no-op. |
| 4 | `70.backend/backend/opencl_backend.spl:346` | emits a `//` comment; `opencl_backend.spl:90` greps for that comment, so partial detection exists but the emitter has no sink. |

**(b) runtime trap emitted, build still rc=0:**

| # | site | note |
|---|---|---|
| 6 | `70.backend/backend/lua_backend.spl:310` | emits `error("lua backend: unsupported instruction")` into generated Lua. |
| 7 | `70.backend/backend/native/isel_riscv64.spl:343` (helper :155) | returns `ISelInstResult`, so an error channel EXISTS, but the message drops the variant name. |

**Backends that already fail CLOSED, for contrast:** VHDL
(`vhdl_validation.spl:457/477/538`, `_VhdlProcess/process_codegen.spl:489`)
returns `Err(CompileError)`; `70.backend/codegen.spl:451` calls `self.error(...)`;
`cuda_backend.spl:558` reports the unsupported instruction;
`svmg_lowering.spl` uses `self.fail(...)`.

**The twin question, answered:** the pure-Simple MIR interpreter
(`95.interp/mir_interpreter.spl:753`) does **not** share this defect. It reads
`rt_enum_discriminant`, eprints `E-INTERP-INST-Unknown disc=… at=<span>`, and
returns `InterpError.UnsupportedOperation`. Comments at :229 and :545 record
that it was previously silent and was already remediated. The codegen backends
above are the leftovers of that same lane.

`35.semantics/.../exhaustiveness_validator.spl` is a lint that exists to catch
exactly this class and is evidently not run over Cranelift / WAT / Lua /
OpenCL / llvm-lib. Wiring it over those five is the ratchet that would stop
this recurring.

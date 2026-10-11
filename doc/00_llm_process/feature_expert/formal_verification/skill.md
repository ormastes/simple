# Formal Verification Feature Expert

Start with `doc/04_architecture/simple_formal_verification_2_0.md` and
`.spipe/simple_formal_verification_2_0/state.md`.

Lean success is `model_proven`, not implementation or artifact verification.
The closed claim follows the exact expanded/woven program through VIR, checked
compiler refinement, trust closure, and final artifact identity. Preserve the
`verified` profile above `critical`, fail closed on unknown/stale/missing
evidence, and never weaken existing RISC-V placeholder/RVFI/SBY truth gates.

Implementation entry points:

- profile and truthful status: `src/compiler/common/assurance/`
- Lean checking/trust: `src/compiler/90.tools/verify/`
- MIR-to-Lean: `src/compiler/70.backend/backend/lean_*.spl`
- plan: `doc/03_plan/agent_tasks/simple_formal_verification_2_0.md`

For direct calls, do not grant recursive, effect, or call-contract authority
from a `MirConstValue.Str` callee. `ResolvedDirectCallManifestV1` binds each
post-lowering site to resolver-captured owner/callee SymbolIds and exact
signature/body snapshots; `ResolvedCanonicalModuleClosureV2` and
`ResolvedVerificationIrModuleV2` consume that same hash. The production
lowering path currently rejects `verified` with
`FV2-E-CALL-MANIFEST-PRODUCER` until it records resolver decisions during
lowering and finalizes the manifest post-MIR/pre-VIR. Runtime/generated calls
need an explicit external-boundary contract instead of an internal binding.

Generic substitution: `src/verification/type_inference_compile` must build the
manual `GenericsConstraints` target along with generated `Generics`. Its closed
substitution laws concern the reduced `Ty` model only; the production `MType`
model, generic annotation preservation, owner resolution and native behavior
need independent refinement and execution evidence. See the generics model
design's reduced Lean proof boundary.

Executable model keys use `mt_key_type` / `mt_key_types` / `mk_key`, with
constructor tags and length/arity framing. `mt_render` is diagnostic display
and is not injective for arbitrary names. The executable candidate has focused
delimiter and constructor-collision regressions; require an admitted runtime
test result before accepting it. Model substitution proofs alone do not prove
key-encoding correctness or exact production/model key-string agreement.

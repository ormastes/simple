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

`GenericSubstModel` is an additional manual default target with the actual
three-constructor MType shape, arbitrary application lists and `con "?"` unknown.
Its composition law is unconditional; idempotence needs a closed substitution
range and result closedness additionally needs supported input (all variables
bound, no unknown constant). Dict/list, executable Simple and HIR `by_symbol`
refinement remain unproved. Do not infer key injectivity from display rendering:
closed `Con("Box<i64>")` and `App("Box", [Con("i64")])` collide.

Executable model keys use `mt_key_type` / `mt_key_types` / `mk_key`, with
constructor tags and length/arity framing. `mt_render` is diagnostic display
and is not injective for arbitrary names. The executable candidate has focused
delimiter and constructor-collision regressions; require an admitted runtime
test result before accepting it. Model substitution proofs alone do not prove
key-encoding correctness or exact production/model key-string agreement.

`MonoBoundaryModel` is a further manual default target: a variant never
displaces a same-named type binding, specialized calls have type-owner
arguments, and a module published to MIR has no generic call given complete
mono diagnostics. Source-coded, not yet kernel-built; see plan §12.

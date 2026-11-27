# Trace artifact information and compiler boundaries — 2026-11-03

Status: integration design; no new optional-HIR execution mode is admitted by this document.

## Stable boundaries

The public owner is the Simple V1 trace observer facade; backend IDs, native function pointers, ELF/COFF details and LLVM patch APIs stay private. Compiler semantic selection precedes physical emission. A physical function may have no independent site after optimization; neither source metadata nor a successful build may invent that coverage.

Every retained artifact carries information needed by its consumer. Keep source/tree identity, compiler producer and phase, requested target, actual backend/toolchain, semantic/visibility schema, generic instantiation, lexical owner, calling convention/ABI profile, selection digest and relevant dependency closure distinct. Runtime maps additionally bind final-image build identity, module instance, private sled ABI, physical function/site IDs and admitted observation kinds.

The host that runs the compiler is not the output target. Host availability does not imply target capability: a Linux host can prepare Windows objects without linking Linux tracing into Windows startup. Host probes and target artifacts have separate recorded identities. Missing information returns an explicit unsupported/unknown/error state at the owning boundary; it cannot be replaced by name-only matching, pointer guessing, a default public bit, or a successful no-op.

## HIR and MIR

HIR supplies resolved declaration intent, lexical ownership, exports, types and generic provenance. Existing compiler owners decide its lifetime. MIR consumers must retain their required resolved facts independently of borrowed HIR storage, with versioned stable IDs and generation-bound ownership. Raw pointers into retired HIR are not a metadata contract.

MIR calls and projections preserve exact owner, receiver representation, concrete generic substitution, parameter/result ABI and physical/logical function identity. A builtin numeric conversion must not be rebound to an unrelated user helper by suffix similarity. An ordinary user function or data global with the same spelling must retain its authored identity. Regression tests exercise both sides of this distinction.

User clarification is pending on two different changes:

1. Making HIR optional for a host-side consumer that already has an admitted MIR artifact and its complete metadata.
2. Representing optional hosted-runtime capabilities through the normal HIR/MIR pipeline.

Do not conflate them. The first would require an explicit MIR input-admission mode, complete dependency/metadata schema, ownership/lifetime proof and equivalence fixtures before HIR can be skipped. The second requires target capability resolution before backend imports, with stable unavailable statuses; it does not inherently remove HIR. Existing execution remains unchanged until the intended change is selected and specified.

## Capture and session information

Generation-bearing public handle values are untrusted lookup keys, not authority by construction. An owner-issued resident entry validates incarnation/generation and serializes control requests. Code, maps and providers remain resident; logical release cannot unload executable code. One process-wide capture session is the baseline.

Canonical events use an explicitly sized/versioned codec rather than the language struct layout. Structural byte decoding cannot prove session authority, monotonic clocks, full coverage, live patch safety or exact spans. Raw records preserve observed edges, transition/loss/unmatched/truncated states and an invalid zero span token. Paired mode is separately admitted and cannot be inferred by reconstructing a plausible stack.

A serial session reference implementation is not a concurrent callback lifetime proof. Native admission/reservation needs an actual linearization protocol and matching tests before any concurrent capability is advertised. A cold Linux adapter planner is not proof of an executable LLVM handler or preserved CPU state.

## Verification mapping

| Boundary | Positive evidence | Required negative control |
|---|---|---|
| Numeric conversion vs authored symbols | Actual native fixture preserves converted values and user calls/globals | Conflicting private reader with incompatible ABI must never receive the numeric receiver |
| MIR artifact admission | Matching producer, source, target, ABI, selection and dependency identities | Missing/stale/mismatched information rejected before emission/activation |
| Event codec | Golden bytes including upper u64 bits, complete field round trip | Truncation, oversize, bad version/tag/size, reserved data rejected |
| Host/target separation | Cross-target compile/dependency evidence | Windows-off build cannot acquire Linux XRay imports or initialization |
| Session retirement | Native admitted callbacks drain without stale references | Late callback, stale handle, stop/drain self-call, timeout retain safe closed state |

These rows extend the staged plan's API-01, ABI-01/02, MAP-01, LIFE-01 and WIN-OFF-01 gates. Source tests and documentation remain UNRUN until real assertions execute on the appropriately admitted producer. Native Mac, ARM64 Linux and Windows profiles qualify independently.

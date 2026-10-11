# Declared enum payloads rejected empty collections

`SdnValue.Array([])` and `SdnValue.Dict({})` failed pure MIR lowering because empty literals inherited default integer element metadata before the declared payload type was checked. Nested literals such as `[[], [1]]` had the same failure. This blocked the HAL source closure and native cache-owner diagnostics.

The repair passes the declared nongeneric payload type through the existing array/dictionary emitters. Each literal child is lowered once, checked against its declared slot, and numerically adapted when supported. The emitted MIR container type and runtime element metadata agree with the declared type. No shared expected-type state is introduced. Generic owners retain their existing inference path; explicitly typed variables and casts keep their type authority and remain rejected when incompatible.

HIR's ArrayLit hint for an empty literal is synthesized by the frontend, not a user ascription. Concrete dictionary hints are still checked. Ordinary expression lowering remains unchanged outside the contextual path.

## Reproduction and evidence

- Executable specification: `test/01_unit/compiler/mir/contextual_enum_payload_spec.spl`.
- Native fixture: `test/fixtures/compiler/contextual_enum_payload/main.spl`.
- Matched reference source: `83bb552bcbfa98629bed63edd7eed6335cea0f9a`.
- Source patch SHA256: `07c41e82b32bab6b99ccf2739c5a7ec05f251c6df2f1c3a3a2a148a85086ea83`.
- Frozen diagnostic host SHA256: `74d7b3816b8fbec69c21aaaf63a5f8250f8b210a581803f69d97ec4f7a641140`.
- Identical 19-case source tests: baseline 8 PASS / 11 FAIL; candidate 19 PASS, no skips or dropped cases. All three baseline owners were verified against the reference revision.
- Actual pure frontend → HIR → MIR → Cranelift adapter emitted the native fixture. Canonical native link and execution returned zero with closed process jobs. Checks cover float insertion/access, nested array mutation and sibling independence, dictionary text-key lookup with nested float values, and tuple payload decoding.
- Native runtime archive SHA256: `07484f4e0da643ae40d036212219d8c365ecd5b7e21d9d74ea276bcb2b0bf26f`. Successful symbol inspection established no required module initializer before using the canonical entry generator.

Local retained evidence packet: `build/enum-contextual-payload-20261010` in the isolated PERF checkout. `verification.json` pins the loaded source owners, projection inventory, emitted object, executable, entry source and runtime providers. Verification receipt SHA256: `345ae55f45aa9af51e0707657e9486a71d96076417ecddc12f2374fc21d80042`.

The native test host executes actual pure compiler source with disclosed mixed dependency modules; it is not a newly qualified self-hosted compiler. Earlier projection mismatches are preserved separately and corrected before attribution: the first source baseline used an older literal emitter, and the first native attempt lacked a provider-metadata helper. No production semantic workaround was used to suppress those failures.

## Open validation

Full self-hosted compiler checks, LLVM execution, real SDN/HAL closure compilation, and allocation/RSS scaling remain unverified. The single native RSS sample is not leak or performance evidence. Direct-HIR nonnil dictionary-hint tests remain open because the source parser currently emits nil hints. Separate bare-variant, missing enum identity and text-conversion failures are outside this repair.

The PR preserves subsequent release changes in the three touched owners on base `2a009604d4561bcff7bd18e3faef2a23afb40ed3`. A distinct final native emission/link/run used those exact composed owners and the same operation fixture, passed with exit0/quiescent1, and is pinned separately in `pr-native-verification.json` (SHA256 `e676dee0553db57e5c74065cc73731692af0089d562077ff3d7cd122f8e50d45`). No claim is made that the earlier 19-case matched comparison ran against every newer dependency.

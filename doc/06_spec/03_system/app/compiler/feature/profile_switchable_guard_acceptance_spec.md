# Attributed collection guard acceptance

This is an authored manual for `test/03_system/app/compiler/feature/profile_switchable_guard_acceptance_spec.spl`. SPipe generation and execution are pending an admitted, source-matched pure-Simple Stage 4 compiler. No result below is a recorded PASS.

The suite entry invokes the repository's `stage4_verify_candidate_provenance` once against the exact executable, its `.provenance.env`, and this source tree. The verifier checks the current source revision; each scenario rechecks candidate and receipt hashes. Absence, refusal or changed bytes fail MissingEvidence. The accepted identity is retained under `build/test-artifacts/stage4-source-admission-<pid>.txt`.

The admission command requires `sh` on the runner's `PATH` (for Windows, the Git POSIX shell is sufficient). A missing shell is MissingEvidence, not a product behavior failure.

## Factory results must match the attributed family

**Reject wrong-family, generic and scalar factories.** Prepare three annotated declarations whose typed factories return an adaptive text map for a text set, a generic set for a generic map, and text for a text set. Compile each fixture with the production `check` command. Each command must fail with its matching `attributed collection factory returns … expected …` diagnostic. A parse error, import failure, timeout, or unrelated compiler failure does not satisfy this scenario. Preserve each command's exit and output under `build/test-artifacts/compiler/factory-guard-<case>-<pid>.txt`.

**Keep an ordinary user-defined same-name method distinct.** A local class named `AdaptiveTextSet` supplies its own `attributed_at_site` method, accepting a map factory and returning its custom type. Call that method directly, compile and run it through the production compiler, and observe its custom result. No stdlib factory-family diagnostic may appear. Preserve the check and run output under `build/test-artifacts/compiler/same-name-factory-<pid>.txt`.

**Reject an annotated user-defined same-name type.** Apply `@collection_algorithm` to that local class. Its leaf name alone cannot grant compiler-owned storage selection. Production compilation must refuse it with an `unsupported attributed container` diagnostic, preserved under `build/test-artifacts/compiler/factory-guard-custom-<pid>.txt`. This typed-provenance behavior is part of the remaining item 7 implementation and is an expected red contract until it lands.

**Preserve an official imported alias.** Import the official adaptive text set under a local name. Apply `@collection_algorithm("hash")`, compile and run it in both interpreter and LLVM native modes, and require the selected hash algorithm and logical set membership. The fixture prints `ALIASED_COLLECTION_FACTORY: PASS` only after both checks. Preserve the two executions and native build output under `build/test-artifacts/compiler/aliased-factory-<pid>.txt`. The current parser recognizes only literal family names at this rewrite, so this scenario is an expected red contract until alias admission is implemented and executed.

**Preserve a re-exported factory.** Import a typed factory from another test module, apply the ordered algorithm to the official adaptive text set, and run both engines. The fixture prints `REEXPORTED_COLLECTION_FACTORY: PASS` only after checking selected storage and sorted values. Preserve the compile and execution output under `build/test-artifacts/compiler/reexported-factory-<pid>.txt`.

## Embedded evidence is validated before forced storage

**Reject malformed feedback under forced policy.** Construct source-matched text and generic containers. Embed an impossible single-sample hit/miss count in a text set, a zero sample count in a generic map, and a hash-probe sample missing its paired collision count in another text set. Each fixture explicitly forces `hash` or `ordered`; all must still fail during production container construction with `embedded collection workload does not match container site and target`. No `UNREACHABLE_…` marker may appear. Preserve each execution under `build/test-artifacts/compiler/profile-guard-<case>-<pid>.txt`.

**Reject a profile from another source.** Capture a real workload profile from the canonical collection CLI probe. Then request a native build of a different entry source with that profile and the same workload and target. The build must fail with `collection profile was not admitted: incompatible`, leave no binary, and preserve capture/build output under `build/test-artifacts/compiler/profile-source-mismatch-<pid>.txt`.

The existing canonical profile-switchable system spec separately exercises exact-site valid feedback, stale site and target refusal, forced-policy precedence, generic semantics, profile capture, and native replay. This focused manual adds production compiler diagnostics and malformed-profile refusal. Runtime admission, actual executed scenario count, deliberate-red calibration, and generated-manual completeness remain open gates.

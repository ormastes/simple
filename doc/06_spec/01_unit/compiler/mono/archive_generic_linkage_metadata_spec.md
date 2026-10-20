# Archive signature effect correspondence

REQ-MONO-ARCHIVE-EFFECTS-001; generic formal hardening plan G1/G2/G5/G7 and section6.

Five added scenarios exercise real retained/archive direct calls, actual inherent-method rewriting, HIR module codec roundtrip before archive projection, and registration-row identity changes for ordered effects/provenance. Rewritten callee stamps and archived specialized signatures must retain IO, Throws<i64>, Custom in that order and their source spans.

Executable owner: `test/01_unit/compiler/mono/archive_generic_linkage_metadata_spec.spl`. Existing scenarios are retained. Authored manual/source only: compiler, native/interpreter, SSpec, docgen and memory/performance measurements UNRUN. No test or compiler was launched. These fixtures use existing APIs and runner; there is no alternative proof or harness.

The actual `test/fixtures/compiler/hir_mono_archive/main.spl` consumer fixture additionally mutates only effects in a real publication delta. Applying that altered receipt must fail without state mutation, and the original unmodified receipt must still apply. It uses the existing owned archive/runtime admission setup and remains UNRUN. The previously stale fixture stage expectation is corrected from v1 to the already-existing production stage v2; no stage protocol change is introduced.

Scope: ordered effects and provenance are source-bound signature facts. Existing source/module authority still supplies nominal meaning. No semantic equivalence across unrelated symbol tables or full structural specialization-key closure is claimed. The summary has no HirFunction body or default-expression fields; only types/type-parameters/effects are retained.

A direct malformed-node control uses an explicit unsafe fixture to refuse absent effect/kind/Throws type/kind at the new signature/transport boundary. Generated codecs preserve some nullable fields and are not semantic admission by themselves. This negative is also UNRUN.

Language invariant: Simple fallible source code uses Result<T,E> and `?`; this patch introduces no throw, try/catch, exception grammar or runtime throwing behavior. `EffectKind.Throws` is only the existing internal HIR metadata name. Fault-injected API tests exercise that representation, not source-level exceptions.

Malformed effect signature digests now propagate refusal through the three existing parent state/delta signature loops, matching registration's existing behavior. The actual archive consumer fixture checks malformed delta, template-facts state and specialized state identities, refuses application without state mutation, then successfully applies the original receipt. No caller-provided authority replaces the actual fixture repository. These additional controls remain UNRUN.

# Archive signature effect correspondence

REQ-MONO-ARCHIVE-EFFECTS-001; generic formal hardening plan G1/G2/G5/G7 and section6.

The existing projection-parity scenario now starts with IO and generic Throws effects. It requires two retained effects and parity with actual full canonicalization, while the original complete function digest remains unchanged, including executable body and parameter default.

Executable owner: `test/01_unit/compiler/mono/retained_template_demand_spec.spl`. Existing scenarios are retained. Authored manual/source only: compiler, native/interpreter, SSpec, docgen and memory/performance measurements UNRUN. No test or compiler was launched. These fixtures use existing APIs and runner; there is no alternative proof or harness.

The actual `test/fixtures/compiler/hir_mono_archive/main.spl` consumer fixture additionally mutates only effects in a real publication delta. Applying that altered receipt must fail without state mutation, and the original unmodified receipt must still apply. It uses the existing owned archive/runtime admission setup and remains UNRUN. The previously stale fixture stage expectation is corrected from v1 to the already-existing production stage v2; no stage protocol change is introduced.

Scope: ordered effects and provenance are source-bound signature facts. Existing source/module authority still supplies nominal meaning. No semantic equivalence across unrelated symbol tables or full structural specialization-key closure is claimed. The summary has no HirFunction body or default-expression fields; only types/type-parameters/effects are retained.

Language invariant: Simple fallible source code uses Result<T,E> and `?`; this patch introduces no throw, try/catch, exception grammar or runtime throwing behavior. `EffectKind.Throws` is only the existing internal HIR metadata name. Fault-injected API tests exercise that representation, not source-level exceptions.

Malformed effect signature digests now propagate refusal through the three existing parent state/delta signature loops, matching registration's existing behavior. The actual archive consumer fixture checks malformed delta, template-facts state and specialized state identities, refuses application without state mutation, then successfully applies the original receipt. No caller-provided authority replaces the actual fixture repository. These additional controls remain UNRUN.

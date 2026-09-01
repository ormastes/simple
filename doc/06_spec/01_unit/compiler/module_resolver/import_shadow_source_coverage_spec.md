# import_shadow_source_coverage_spec

> Purpose: Prove that ambiguity map covers every searched location and module shape.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# import_shadow_source_coverage_spec

Purpose: Prove that ambiguity map covers every searched location and module shape.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that ambiguity map covers every searched location and module shape.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### ambiguity map covers every searched location and module shape

#### flags a bare root .spl file colliding with a tier file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- flags a bare root .spl file colliding with a tier file
- Verify: flags a bare root .spl file colliding with a tier file
   - Expected: r.tier_multiplicity["alpha"].len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a bare root .spl file colliding with a tier file")
step("Verify: flags a bare root .spl file colliding with a tier file")
# @req: REQ-COMPILER-MODULE-RESOLVER-001
var r = fixture_map()
expect(r.tier_multiplicity["alpha"].len()).to_equal(2)
expect(r.tier_multiplicity["alpha"]).to_contain("<lib-root>")
```

</details>

#### flags a nested root path colliding with a tier path

- flags a nested root path colliding with a tier path
- Verify: flags a nested root path colliding with a tier path
   - Expected: r.tier_multiplicity["deep.inner.leaf"].len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a nested root path colliding with a tier path")
step("Verify: flags a nested root path colliding with a tier path")
var r = fixture_map()
expect(r.tier_multiplicity["deep.inner.leaf"].len()).to_equal(2)
expect(r.tier_multiplicity["deep.inner.leaf"]).to_contain("<lib-root>")
```

</details>

#### flags a root package directory colliding with a tier package

- flags a root package directory colliding with a tier package
- Verify: flags a root package directory colliding with a tier package
   - Expected: r.tier_multiplicity["pkg"].len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a root package directory colliding with a tier package")
step("Verify: flags a root package directory colliding with a tier package")
var r = fixture_map()
expect(r.tier_multiplicity["pkg"].len()).to_equal(2)
expect(r.tier_multiplicity["pkg"]).to_contain("<lib-root>")
```

</details>

#### does not manufacture ambiguity for a root-only module

- does not manufacture ambiguity for a root-only module
- Verify: does not manufacture ambiguity for a root-only module
   - Expected: r.tier_multiplicity["lonely"].len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not manufacture ambiguity for a root-only module")
step("Verify: does not manufacture ambiguity for a root-only module")
var r = fixture_map()
expect(r.tier_multiplicity["lonely"].len()).to_equal(1)
```

</details>

#### does not re-register tier directories as root modules

- does not re-register tier directories as root modules
- Verify: does not re-register tier directories as root modules
   - Expected: r.tier_multiplicity.contains_key("common.alpha") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("does not re-register tier directories as root modules")
step("Verify: does not re-register tier directories as root modules")
# A tier dir must be walked as a tier, never also as `<lib-root>`;
# otherwise every tier module would look self-ambiguous.
var r = fixture_map()
expect(r.tier_multiplicity.contains_key("common.alpha")).to_equal(false)
```

</details>

#### flags a real collision in the actual src/lib tree

- flags a real collision in the actual src/lib tree
- Verify: flags a real collision in the actual src/lib tree
   - Expected: r.tier_multiplicity["text"].len() >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("flags a real collision in the actual src/lib tree")
step("Verify: flags a real collision in the actual src/lib tree")
# src/lib/text.spl and src/lib/common/text.spl both exist.
var r = moduleresolver_new(".", "src")
r.build_tier_multiplicity("src/lib")
expect(r.tier_multiplicity["text"].len() >= 2).to_equal(true)
expect(r.tier_multiplicity["text"]).to_contain("<lib-root>")
```

</details>

#### the direct src/lib/<path> resolve step is wired to the diagnostic

- the direct src/lib/<path> resolve step is wired to the diagnostic
- Verify: the direct src/lib/<path> resolve step is wired to the diagnostic
   - Expected: _scan("self\\.maybe_warn_tier_ambiguity\\(root_lib_dir, inner_segments, from_file\\)").len() > 0 is true
   - Expected: _scan("fn collect_lib_root_modules\\(lib_dir: text, tier_names: \\[text\\]\\):").len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("the direct src/lib/<path> resolve step is wired to the diagnostic")
step("Verify: the direct src/lib/<path> resolve step is wired to the diagnostic")
# The step that produced the silent case must call the warning too,
# non-fatally, on its Ok path.
expect(_scan("self\\.maybe_warn_tier_ambiguity\\(root_lib_dir, inner_segments, from_file\\)").len() > 0).to_equal(true)
expect(_scan("fn collect_lib_root_modules\\(lib_dir: text, tier_names: \\[text\\]\\):").len() > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
- `REQ-COMPILER-MODULE-RESOLVER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fc4a15b20f0c4b79742ba6768906acd34849534054fdd81456e0fc644334a55e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fc4a15b20f0c4b79742ba6768906acd34849534054fdd81456e0fc644334a55e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fc4a15b20f0c4b79742ba6768906acd34849534054fdd81456e0fc644334a55e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.spl
mirror: doc/06_spec/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a bare root .spl file colliding with a tier file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a nested root path colliding with a tier path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/module_resolver/import_shadow_source_coverage_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags a root package directory colliding with a tier package' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

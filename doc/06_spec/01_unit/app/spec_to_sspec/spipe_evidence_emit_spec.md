# spec-to-sspec evidence extension adapter

> evidence-bearing scenarios detected by the spec-to-sspec modernizer into a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# spec-to-sspec evidence extension adapter

evidence-bearing scenarios detected by the spec-to-sspec modernizer into a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Purpose and audience:** verifies `spipe_evidence_emit.spl` (Lane E6) projects
evidence-bearing scenarios detected by the spec-to-sspec modernizer into a
well-formed `SpipeEvidenceExtension` envelope, and that `extension_is_wellformed`
rejects a malformed envelope the spec constructs directly.

## Scenarios

### spec-to-sspec spipe evidence extension adapter

#### emits one interaction_case node per evidence-bearing scenario

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits one interaction_case node per evidence-bearing scenario
- scan a synthetic spec source with one evidence-bearing scenario
   - Expected: nodes.len() equals `1`
   - Expected: nodes[0].kind equals `SpipeEvidenceNodeKind.interaction_case`
   - Expected: nodes[0].semantic_id equals `synthetic_spec.spl#captures output`
   - Expected: nodes[0].adapter_rule_id equals `spec-to-sspec.evidence-scan.v1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("emits one interaction_case node per evidence-bearing scenario")
step("scan a synthetic spec source with one evidence-bearing scenario")
val source = "describe \"d\":\n    it \"captures output\":\n        capture_tui_grid()\n        expect(1).to_equal(1)\n"
val nodes = spipe_evidence_nodes_for_source("synthetic_spec.spl", source)
expect(nodes.len()).to_equal(1)
expect(nodes[0].kind).to_equal(SpipeEvidenceNodeKind.interaction_case)
expect(nodes[0].semantic_id).to_equal("synthetic_spec.spl#captures output")
expect(nodes[0].adapter_rule_id).to_equal("spec-to-sspec.evidence-scan.v1")
```

</details>

#### skips scenarios with no evidence-bearing calls

- skips scenarios with no evidence-bearing calls
- scan a synthetic spec source with an assertion-only scenario
   - Expected: nodes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("skips scenarios with no evidence-bearing calls")
step("scan a synthetic spec source with an assertion-only scenario")
val source = "describe \"d\":\n    it \"pure check\":\n        expect(1).to_equal(1)\n"
val nodes = spipe_evidence_nodes_for_source("synthetic_spec.spl", source)
expect(nodes.len()).to_equal(0)
```

</details>

#### produces a well-formed extension envelope for a real scan

- produces a well-formed extension envelope for a real scan
- build the full envelope from a synthetic source
   - Expected: extension.namespace_id equals `simple.sspec.evidence.ext.v1`
   - Expected: extension_is_wellformed(extension) is true
   - Expected: extension_wellformed_reason(extension) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("produces a well-formed extension envelope for a real scan")
step("build the full envelope from a synthetic source")
val source = "describe \"d\":\n    it \"captures output\":\n        capture_tui_grid()\n        expect(1).to_equal(1)\n"
val extension = spipe_evidence_extension_for_source("synthetic_spec.spl", source)
expect(extension.namespace_id).to_equal("simple.sspec.evidence.ext.v1")
expect(extension_is_wellformed(extension)).to_equal(true)
expect(extension_wellformed_reason(extension)).to_equal("")
```

</details>

#### serializes sidecar content deterministically

- serializes sidecar content deterministically
- render sidecar text twice for identical input
   - Expected: first equals `second`
   - Expected: first contains `namespace_id: simple.sspec.evidence.ext.v1`
   - Expected: first contains `node.kind: interaction_case`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("serializes sidecar content deterministically")
step("render sidecar text twice for identical input")
val source = "describe \"d\":\n    it \"captures output\":\n        capture_tui_grid()\n        expect(1).to_equal(1)\n"
val first = spipe_evidence_sidecar_content("synthetic_spec.spl", source)
val second = spipe_evidence_sidecar_content("synthetic_spec.spl", source)
expect(first).to_equal(second)
expect(first.contains("namespace_id: simple.sspec.evidence.ext.v1")).to_equal(true)
expect(first.contains("node.kind: interaction_case")).to_equal(true)
```

</details>

#### rejects a malformed envelope built with an empty semantic id

- rejects a malformed envelope built with an empty semantic id
- construct an envelope with an invalid node directly
   - Expected: extension_is_wellformed(extension) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a malformed envelope built with an empty semantic id")
step("construct an envelope with an invalid node directly")
val bad_node = spipe_evidence_node(
    "",
    SpipeEvidenceNodeKind.interaction_case,
    0,
    1,
    "",
    "rule",
    "kept",
    "payload"
)
val extension = spipe_evidence_extension([bad_node])
expect(extension_is_wellformed(extension)).to_equal(false)
expect(extension_wellformed_reason(extension)).to_contain("empty semantic id")
```

</details>

#### rejects a malformed envelope with a non-positive span

- rejects a malformed envelope with a non-positive span
- construct an envelope with span_end <= span_start
   - Expected: extension_is_wellformed(extension) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a malformed envelope with a non-positive span")
step("construct an envelope with span_end <= span_start")
val bad_node = spipe_evidence_node(
    "id-1",
    SpipeEvidenceNodeKind.interaction_case,
    5,
    5,
    "",
    "rule",
    "kept",
    "payload"
)
val extension = spipe_evidence_extension([bad_node])
expect(extension_is_wellformed(extension)).to_equal(false)
expect(extension_wellformed_reason(extension)).to_contain("non-positive span")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SPEC-TO-SPIPE-EVIDENCE-EXT-001`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1a2f70220d559101d6e121a2e759bdfdea28f5f824670dffd2d267afe7bcc51f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1a2f70220d559101d6e121a2e759bdfdea28f5f824670dffd2d267afe7bcc51f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1a2f70220d559101d6e121a2e759bdfdea28f5f824670dffd2d267afe7bcc51f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.spl
mirror: doc/06_spec/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=80
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips scenarios with no evidence-bearing calls' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a malformed envelope built with an empty semantic id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spec_to_sspec/spipe_evidence_emit_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a malformed envelope with a non-positive span' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

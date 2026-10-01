# scv_tree_agreement_spec

> Purpose: This spec proves `scv promote-verify --git <path>` enforces exact tree

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# scv_tree_agreement_spec

Purpose: This spec proves `scv promote-verify --git <path>` enforces exact tree

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_tree_agreement_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: This spec proves `scv promote-verify --git <path>` enforces exact tree
agreement (Git == SCV, byte for byte) BEFORE and AFTER a promotion is recorded
(SCV-MIG-15, scv_v2_final_report §16.2): agreement on both sides publishes a
promotion record with the backend mapping row; any divergence is a FAIL and
nothing is marked published.
Audience: Maintainers of the SCV migration promotion path.

## Scenarios

### scv promote-verify

#### publishes only after exact tree agreement holds before and after promotion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes only after exact tree agreement holds before and after promotion
- Run promote-verify against a byte-identical git mirror
- Verify pre and post comparisons both passed and the promotion is published


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("publishes only after exact tree agreement holds before and after promotion")
step("Run promote-verify against a byte-identical git mirror")
var lines = _prelude("match")
lines.push("scv promote-verify --git \"$TMP/mirror\"")
lines.push("printf 'pv_code=%s\\n' \"$?\"")
lines.push("cat .scv/meta/promotion.sdn")
lines.push("cat .scv/meta/backend_map.sdn | head -4")
val out = _run(lines)
step("Verify pre and post comparisons both passed and the promotion is published")
expect(out).to_contain("pre: ")
expect(out).to_contain("post: ")
expect(out).to_contain("PASS — exact tree agreement verified before and after promotion")
expect(out).to_contain("published: true")
expect(out).to_contain("backend_map:")
expect(out).to_contain("pv_code=0")
expect(out).to_contain("exit=0")
```

</details>

#### is idempotent: a re-run over an unchanged pair still publishes cleanly

- is idempotent: a re-run over an unchanged pair still publishes cleanly
- Run promote-verify twice against the same matching mirror
- Verify the second run reaches the same PASS verdict


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("is idempotent: a re-run over an unchanged pair still publishes cleanly")
step("Run promote-verify twice against the same matching mirror")
var lines = _prelude("idem")
lines.push("scv promote-verify --git \"$TMP/mirror\" >/dev/null")
lines.push("scv promote-verify --git \"$TMP/mirror\"")
lines.push("printf 'pv_code=%s\\n' \"$?\"")
val out = _run(lines)
step("Verify the second run reaches the same PASS verdict")
expect(out).to_contain("PASS — exact tree agreement verified before and after promotion")
expect(out).to_contain("pv_code=0")
expect(out).to_contain("exit=0")
```

</details>

#### fails and marks nothing published when the git tree diverged

- fails and marks nothing published when the git tree diverged
- Diverge the git mirror, then attempt promote-verify
- Verify the FAIL verdict, exit 1, and the absent promotion record


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fails and marks nothing published when the git tree diverged")
step("Diverge the git mirror, then attempt promote-verify")
var lines = _prelude("diverge")
lines.push("printf 'ALPHA\\n' > \"$TMP/mirror/a.txt\"")
lines.push("git -C \"$TMP/mirror\" add -A")
lines.push("git -C \"$TMP/mirror\" -c user.email=t@t -c user.name=t commit -q -m diverge")
lines.push("set +e")
lines.push("scv promote-verify --git \"$TMP/mirror\"")
lines.push("printf 'pv_code=%s\\n' \"$?\"")
lines.push("set -e")
lines.push("test -f .scv/meta/promotion.sdn && echo promotion_record=present || echo promotion_record=absent")
val out = _run(lines)
step("Verify the FAIL verdict, exit 1, and the absent promotion record")
expect(out).to_contain("bytes differ: a.txt")
expect(out).to_contain("FAIL — promotion blocked: pre-promotion tree disagreement; nothing marked published")
expect(out).to_contain("pv_code=1")
expect(out).to_contain("promotion_record=absent")
expect(out).to_contain("exit=0")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SCV-TREE-AGREEMENT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `355d3764bc975068e2126d71951ea61308072e6fa96f8b21f48fb57465bb8846`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `355d3764bc975068e2126d71951ea61308072e6fa96f8b21f48fb57465bb8846`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `355d3764bc975068e2126d71951ea61308072e6fa96f8b21f48fb57465bb8846`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/integration/app/scv_tree_agreement_spec.spl
mirror: doc/06_spec/integration/app/scv_tree_agreement_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/integration/app/scv_tree_agreement_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_tree_agreement_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_tree_agreement_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/integration/app/scv_tree_agreement_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes only after exact tree agreement holds before and after promotion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_tree_agreement_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is idempotent: a re-run over an unchanged pair still publishes cleanly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_tree_agreement_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails and marks nothing published when the git tree diverged' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Scoring Specification

> Tests covering SSpec maintenance scoring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scoring Specification

## Scenarios

### SSpec maintenance scoring

#### caps blockers and explains deductions across weak dimensions

- Verify: caps blockers and explains deductions across weak dimensions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: caps blockers and explains deductions across weak dimensions")
val report = analyze_sspec_text("weak_spec.spl", "describe \"weak\":\n    it \"is unresolved\":\n        pass_todo\n")
expect(report.score.raw_aggregate).to_be_greater_than(report.score.effective_aggregate)
expect(report.score.effective_aggregate).to_be_less_than(50)
expect(report.score.blocker_count).to_be_greater_than(0)
expect(report.findings.len()).to_be_greater_than(5)
```

</details>

#### awards all seven dimensions only to professional structural facts

- Verify: awards all seven dimensions only to professional structural facts
   - Expected: report.score.effective_aggregate equals `100`
   - Expected: report.findings.len() equals `0`
   - Expected: report.scenario_count equals `1`
   - Expected: report.real_assertion_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: awards all seven dimensions only to professional structural facts")
val report = analyze_sspec_text("good_spec.spl", professional_source())
expect(report.score.effective_aggregate).to_equal(100)
expect(report.findings.len()).to_equal(0)
expect(report.scenario_count).to_equal(1)
expect(report.real_assertion_count).to_equal(1)
```

</details>

#### rejects an arithmetic tautology as a real oracle

- Verify: rejects an arithmetic tautology as a real oracle
   - Expected: report.real_assertion_count equals `0`
   - Expected: report.score.blocker_count equals `2`
   - Expected: finding_ids(report) contains `SSDOC-ORA-001`
   - Expected: finding_ids(report) contains `SSDOC-ORA-002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: rejects an arithmetic tautology as a real oracle")
val source = professional_source().replace("expect(production_result).to_equal(\"ready\")",
    "expect(1).to_equal(1)")
val report = analyze_sspec_text("tautology_spec.spl", source)
expect(report.real_assertion_count).to_equal(0)
# A tautology legitimately trips BOTH blockers: ORA-001 (no real
# assertion survived) and ORA-002 (locally constructed arithmetic).
expect(report.score.blocker_count).to_equal(2)
expect(finding_ids(report).contains("SSDOC-ORA-001")).to_equal(true)
expect(finding_ids(report).contains("SSDOC-ORA-002")).to_equal(true)
```

</details>

#### extracts scenario source and rendered manual facts separately

- Verify: extracts scenario source and rendered manual facts separately
   - Expected: source_facts.step_count equals `1`
   - Expected: source_facts.capture_count equals `1`
   - Expected: manual_facts.visible_step_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: extracts scenario source and rendered manual facts separately")
val source_facts = extract_sspec_source_facts("x_spec.spl", professional_source())
val manual_facts = extract_sspec_manual_facts("x_spec.md",
    "# Workflow\n\n1. Exercise production\n\n## Evidence\n\nREQ-001\n\n## Verification\n\n## Troubleshooting\n\nSource SHA-256: abc\n")
expect(source_facts.step_count).to_equal(1)
expect(source_facts.capture_count).to_equal(1)
expect(source_facts.scenarios[0].line).to_be_greater_than(1)
expect(manual_facts.visible_step_count).to_equal(1)
expect(manual_facts.evidence_block_count).to_be_greater_than(0)
```

</details>

#### keeps the stable rule catalog explainable and separate from SPIPE lint

- Verify: keeps the stable rule catalog explainable and separate from SPIPE lint
   - Expected: rules[0].rule_id.starts_with("SSDOC-") is true
   - Expected: sspec_lint_rule_references() equals `[`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: keeps the stable rule catalog explainable and separate from SPIPE lint")
val rules = sspec_rule_definitions()
expect(rules.len()).to_be_greater_than(15)
expect(rules[0].rule_id.starts_with("SSDOC-")).to_equal(true)
expect(rules[0].rationale.len()).to_be_greater_than(10)
expect(rules[0].suppression_policy.len()).to_be_greater_than(10)
expect(sspec_lint_rule_references()).to_equal([
    "SPIPE001", "SPIPE002", "SPIPE003", "SPIPE004", "SPIPE005",
    "SPIPE006", "SPIPE007"])
```

</details>

#### offers a certain EasyFix only for supported mechanical syntax

- Verify: offers a certain EasyFix only for supported mechanical syntax
   - Expected: fixable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: offers a certain EasyFix only for supported mechanical syntax")
val report = analyze_sspec_text("fix_spec.spl", "@step Do work\n" + professional_source())
var fixable = false
for finding in report.findings:
    if finding.rule_id == "SSDOC-MNT-003":
        fixable = finding.fixable and finding.safe_fix_id == "SSDOC-MNT-003"
expect(fixable).to_equal(true)
expect(render_json_report(report)).to_contain("\"replacements\":[")
expect(render_sarif_report(report)).to_contain("\"fixes\":[")
```

</details>

#### keeps fingerprints stable across unrelated line movement and applies baselines

- Verify: keeps fingerprints stable across unrelated line movement and applies baselines
   - Expected: first.findings[0].fingerprint equals `moved.findings[0].fingerprint`
   - Expected: analyze_sspec_text("./weak_spec.spl", "describe \"weak\":\n    it \"is unresolved\":\n        pass_todo\n").source_path equals `weak_spec.spl`
   - Expected: based.findings[0].baseline_state equals `unchanged`
   - Expected: based.resolved_fingerprints equals `["resolved-id"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: keeps fingerprints stable across unrelated line movement and applies baselines")
val first = analyze_sspec_text("weak_spec.spl", "describe \"weak\":\n    it \"is unresolved\":\n        pass_todo\n")
val moved = analyze_sspec_text("weak_spec.spl", "\n\ndescribe \"weak\":\n    it \"is unresolved\":\n        pass_todo\n")
expect(first.findings[0].fingerprint).to_equal(moved.findings[0].fingerprint)
expect(analyze_sspec_text("./weak_spec.spl", "describe \"weak\":\n    it \"is unresolved\":\n        pass_todo\n").source_path).to_equal("weak_spec.spl")
val based = baseline_sspec_report(first, [first.findings[0].fingerprint, "resolved-id"])
expect(based.findings[0].baseline_state).to_equal("unchanged")
expect(based.resolved_fingerprints).to_equal(["resolved-id"])
```

</details>

#### marks missing stale and current mirrors from content identities

- Verify: marks missing stale and current mirrors from content identities
   - Expected: analyze_sspec_pair_text("test/x_spec.spl", source, None).mirror_state equals `missing`
   - Expected: analyze_sspec_pair_text("test/x_spec.spl", source, Some("old")).mirror_state equals `stale`
   - Expected: analyze_sspec_pair_text("test/x_spec.spl", source, Some(manual)).mirror_state equals `current`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: marks missing stale and current mirrors from content identities")
val source = professional_source()
val report = analyze_sspec_text("test/x_spec.spl", source)
expect(analyze_sspec_pair_text("test/x_spec.spl", source, None).mirror_state).to_equal("missing")
expect(analyze_sspec_pair_text("test/x_spec.spl", source, Some("old")).mirror_state).to_equal("stale")
val manual = "# Workflow\n1. Exercise\n## Evidence\n## Verification\n## Troubleshooting\nSource SHA-256: {report.source_hash}\nREQ-001\n"
expect(analyze_sspec_pair_text("test/x_spec.spl", source, Some(manual)).mirror_state).to_equal("current")
```

</details>

#### renders deterministic full JSON and SARIF metadata

- Verify: renders deterministic full JSON and SARIF metadata
   - Expected: render_json_report(report) equals `json`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: renders deterministic full JSON and SARIF metadata")
val report = baseline_sspec_report(analyze_sspec_text("weak_spec.spl",
    "describe \"weak\":\n    it \"is unresolved\":\n        pass_todo\n"), [])
val json = render_json_report(report)
val sarif = render_sarif_report(report)
expect(render_json_report(report)).to_equal(json)
expect(json).to_contain("\"baseline_state\":\"new\"")
expect(json).to_contain("\"score_deduction\"")
expect(sarif).to_contain("\"rules\":[")
expect(sarif).to_contain("\"locations\":[")
expect(sarif).to_contain("\"baselineState\":\"new\"")
```

</details>

#### keeps cache identities deterministic

- Verify: keeps cache identities deterministic
   - Expected: a equals `b`
   - Expected: sspec_finding_baseline_state("x", ["x"]) equals `unchanged`
   - Expected: sspec_resolved_fingerprints(["x"], ["x", "y"]) equals `["y"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: keeps cache identities deterministic")
val a = sspec_cache_identity("a", "source", "mirror", "rules", "config", "tool")
val b = sspec_cache_identity("a", "source", "mirror", "rules", "config", "tool")
expect(a).to_equal(b)
expect(sspec_finding_baseline_state("x", ["x"])).to_equal("unchanged")
expect(sspec_resolved_fingerprints(["x"], ["x", "y"])).to_equal(["y"])
```

</details>

#### invalidates every cache identity dimension independently

- Verify: invalidates every cache identity dimension independently


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: invalidates every cache identity dimension independently")
val base = sspec_cache_identity("test/a_spec.spl", "source-a",
    "mirror-a", "rules-a", "config-a", "tool-a")
expect(sspec_cache_identity("test/b_spec.spl", "source-a",
    "mirror-a", "rules-a", "config-a", "tool-a") == base).to_be(false)
expect(sspec_cache_identity("test/a_spec.spl", "source-b",
    "mirror-a", "rules-a", "config-a", "tool-a") == base).to_be(false)
expect(sspec_cache_identity("test/a_spec.spl", "source-a",
    "mirror-b", "rules-a", "config-a", "tool-a") == base).to_be(false)
expect(sspec_cache_identity("test/a_spec.spl", "source-a",
    "mirror-a", "rules-b", "config-a", "tool-a") == base).to_be(false)
expect(sspec_cache_identity("test/a_spec.spl", "source-a",
    "mirror-a", "rules-a", "config-b", "tool-a") == base).to_be(false)
expect(sspec_cache_identity("test/a_spec.spl", "source-a",
    "mirror-a", "rules-a", "config-a", "tool-b") == base).to_be(false)
```

</details>

#### keeps reference scaffolds byte deterministic

- Verify: keeps reference scaffolds byte deterministic
   - Expected: second equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: keeps reference scaffolds byte deterministic")
val reference = "# Reference\n## REQ-017: report status\n" +
    "Action: Run the status probe\nExpected: status is visible\n"
val first = scaffold_reference_text("reference.md", reference)
val second = scaffold_reference_text("reference.md", reference)
expect(second).to_equal(first)
expect(first).to_contain("# Reference SHA-256:")
expect(first).to_contain("REQ-017 <- reference.md:2")
```

</details>

#### detects dangling requirements local arithmetic and unexplained literals

- Verify: detects dangling requirements local arithmetic and unexplained literals


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: detects dangling requirements local arithmetic and unexplained literals")
# REQ-404 is a real # @req comment with no scenario binding (dangling).
# Since 2026-08-22 the scanner skips triple-quoted string content, so a
# REQ id in prose no longer counts as declared.
val source = "# @req: REQ-404\n" +
    "describe \"behavior\":\n    it \"returns a value\":\n" +
    "        step(\"Calculate locally\")\n        val result = 7\n" +
    "        expect(result).to_equal(7)\n"
val ids = finding_ids(analyze_sspec_text("local_spec.spl", source))
expect(ids).to_contain("SSDOC-ORA-002")
expect(ids).to_contain("SSDOC-ORA-003")
expect(ids).to_contain("SSDOC-TRC-003")
```

</details>

#### requires owner and reason and refuses blocker suppression

- Verify: requires owner and reason and refuses blocker suppression
   - Expected: parse_sspec_suppressions("SSDOC-MNT-007||because\n").is_err() is true
   - Expected: apply_sspec_suppressions(report, suppressions).is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: requires owner and reason and refuses blocker suppression")
expect(parse_sspec_suppressions("SSDOC-MNT-007||because\n").is_err()).to_equal(true)
val report = analyze_sspec_text("blocked_spec.spl",
    "describe \"blocked\":\n    it \"has no oracle\":\n        step(\"Run\")\n")
match parse_sspec_suppressions("SSDOC-ORA-001|qa-owner|not acceptable\n"):
    case Err(message): fail(message)
    case Ok(suppressions):
        expect(apply_sspec_suppressions(report, suppressions).is_err()).to_equal(true)
```

</details>

#### composes idempotent professional provenance around the SPipe manual

- Verify: composes idempotent professional provenance around the SPipe manual
   - Expected: second.content equals `first.content`
   - Expected: first.report.mirror_state equals `current`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: composes idempotent professional provenance around the SPipe manual")
val base = "# Feature\n## Purpose and audience\n## Scope and preconditions\n" +
    "## Primary workflow\n1. Exercise production\n## Requirements and traceability\n" +
    "REQ-001\n## Evidence\nCaptured result\n## Verification and outcomes\n" +
    "Ready.\n## Unsupported behavior and limitations\nNone.\n" +
    "## Recovery and troubleshooting\nReview diagnostics.\n"
val first = compose_sspec_documentized_manual(
    "test/good_spec.spl", professional_source(), base, true)
val second = compose_sspec_documentized_manual(
    "test/good_spec.spl", professional_source(), first.content, true)
expect(second.content).to_equal(first.content)
expect(first.content).to_contain("## Generation history")
expect(first.content).to_contain("## SSpec documentization scorecard")
expect(first.report.mirror_state).to_equal("current")
```

</details>

#### reports declared lifecycle paths that no longer resolve

- Verify: reports declared lifecycle paths that no longer resolve


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: reports declared lifecycle paths that no longer resolve")
val source = professional_source().replace("doc/05_design/x.md",
    "doc/05_design/definitely_missing_ssdoc_fixture.md")
val report = inspect_sspec_lifecycle_links(
    analyze_sspec_text("fixture_spec.spl", source), source)
expect(finding_ids(report)).to_contain("SSDOC-MNT-009")
```

</details>

#### rejects overlapping EasyFix replacements before any write

- Verify: rejects overlapping EasyFix replacements before any write
   - Expected: sspec_source_is_stale("before", "after") is true
   - Expected: sspec_source_is_stale("same", "same") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-LOCAL-001
step("Verify: rejects overlapping EasyFix replacements before any write")
var first = EasyFix.create("SSDOC-TEST-1", "first",
    FixConfidence.Certain)
first.add_replacement(Replacement.create("fixture.spl", 0, 4, 1, 1,
    "first"))
var second = EasyFix.create("SSDOC-TEST-2", "second",
    FixConfidence.Certain)
second.add_replacement(Replacement.create("fixture.spl", 2, 6, 1, 3,
    "second"))
expect(apply_sspec_easyfixes_result("fixture.spl", "12345678",
    [first, second]).is_err()).to_equal(true)
expect(sspec_source_is_stale("before", "after")).to_equal(true)
expect(sspec_source_is_stale("same", "same")).to_equal(false)
```

</details>

#### counts parenless check statements as real oracles

- Verify: counts parenless check statements as real oracles
   - Expected: finding_ids(report) does not contain `SSDOC-ORA-001`
   - Expected: finding_ids(tautology) contains `SSDOC-ORA-001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: counts parenless check statements as real oracles")
# The usage-spec family asserts via parenless `check cond` statements —
# the scorer must count them (and parenless `expect_not cond`, the SFFI
# contract form), while still rejecting `check true`.
val body = "describe \"sets\":\n    it \"holds three elements\":\n" +
    "        # @req: REQ-012\n" +
    "        step(\"Build the set\")\n" +
    "        val nums = [1, 2, 3]\n" +
    "        check nums.len() == 3\n" +
    "        expect_not nums.contains(9)\n"
val source = "\"\"\"\n## Purpose and audience\n## Operator workflow\n" +
    "# @manual: primary\nREQ-012\ndoc/01_research/local/x.md\ndoc/03_plan/sys_test/x.md\n" +
    "doc/04_architecture/x.md\ndoc/05_design/x.md\n\"\"\"\n" + body
val report = analyze_sspec_text("parenless_check_spec.spl", source)
expect(report.real_assertion_count).to_be_greater_than(0)
expect(finding_ids(report).contains("SSDOC-ORA-001")).to_equal(false)
val tautology = analyze_sspec_text("tautology_check_spec.spl",
    source.replace("check nums.len() == 3", "check true")
        .replace("expect_not nums.contains(9)", ""))
expect(finding_ids(tautology).contains("SSDOC-ORA-001")).to_equal(true)
```

</details>

#### counts standalone assert_equal/assert_true as real oracles

- Verify: counts standalone assert_equal/assert_true as real oracles
   - Expected: finding_ids(report) does not contain `SSDOC-ORA-001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: counts standalone assert_equal/assert_true as real oracles")
# Binary/domain specs assert via the repo's preferred standalone
# assertions — the scorer must not report ORA-001 "no real executed
# assertion" for them.
val source = "\"\"\"\n## Purpose and audience\n## Operator workflow\n" +
    "# @manual: primary\nREQ-012\ndoc/01_research/local/x.md\ndoc/03_plan/sys_test/x.md\n" +
    "doc/04_architecture/x.md\ndoc/05_design/x.md\n\"\"\"\n" +
    "describe \"word tables\":\n" +
    "    it \"stacks the decoded words in document order\":\n" +
    "        # @req: REQ-012\n" +
    "        step(\"Decode the header word\")\n" +
    "        val rows = stacked_manual_rows(layout, word)\n" +
    "        assert_equal(rows.len(), 2)\n" +
    "        assert_true(rows[0].starts_with(\"W0\"))\n"
val report = analyze_sspec_text("standalone_spec.spl", source)
expect(report.real_assertion_count).to_be_greater_than(0)
expect(finding_ids(report).contains("SSDOC-ORA-001")).to_equal(false)
# The fixture fed to the analyzer must actually exercise the
# standalone-assert form (it is analyzer input, not system evidence).
expect(source.split("assert_equal(").len()).to_be_greater_than(1)
```

</details>

#### scores typed binary and TUI evidence as real captures on both sides

- Verify: scores typed binary and TUI evidence as real captures on both sides
   - Expected: finding_ids(binary_report) does not contain `SSDOC-EVD-001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify: scores typed binary and TUI evidence as real captures on both sides")
# Source side: modern typed-evidence calls (compare_evidence,
# evidence_manifest, binary_layout, terminal_grid) must count as
# captures — regression for the scorer's binary/UI blind spot.
val binary_source = "\"\"\"\n## Purpose and audience\n## Operator workflow\n" +
    "# @manual: primary\nREQ-011\ndoc/01_research/local/x.md\ndoc/03_plan/sys_test/x.md\n" +
    "doc/04_architecture/x.md\ndoc/05_design/x.md\n\"\"\"\n" +
    "describe \"page-table entries\":\n" +
    "    it \"decodes the entry into the documented bit table\":\n" +
    "        # @req: REQ-011\n" +
    "        step(\"Encode the page-table entry\")\n" +
    "        val pte = encode_pte()\n" +
    "        val evidence = decode_u64(pte, pte_layout())\n" +
    "        val result = compare_evidence(evidence, expected_pte_oracle())\n" +
    "        expect(result.passed).to_equal(true)\n" +
    "        val manifest = evidence_manifest(\"sha\", \"run\", [])\n" +
    "        expect(manifest.spec_sha256.len()).to_equal(64)\n"
val binary_report = analyze_sspec_text("binary_spec.spl", binary_source)
expect(binary_report.capture_count).to_be_greater_than(0)
expect(finding_ids(binary_report).contains("SSDOC-EVD-001")).to_equal(false)
# Manual side: the real renderer emits ```text fences (terminal grid),
# ## Provenance, and images — none of which say "textgrid"/"protocol".
val manual = "# Workflow\n\n1. Encode the entry\n\n## Evidence\n\n" +
    "### Bit table\n\n```text\n| bits | value |\n```\n\n" +
    "## Provenance\n\n- spec sha-256: abc\n\n## Verification\n\n" +
    "## Troubleshooting\n\nSource SHA-256: abc\n"
val manual_facts = extract_sspec_manual_facts("binary_spec.md", manual)
expect(manual_facts.evidence_block_count).to_be_greater_than(0)
expect(analyze_sspec_pair_text("binary_spec.spl", binary_source,
    Some(manual + binary_report.source_hash)).mirror_state).to_equal("current")
expect(finding_ids(analyze_sspec_pair_text("binary_spec.spl", binary_source,
    Some(manual + binary_report.source_hash))).contains("SSDOC-EVD-003")).to_equal(false)
# GUI action-trace evidence counts too.
val tui_facts = extract_sspec_source_facts("tui_spec.spl",
    "describe \"surface\":\n    it \"renders the grid\":\n" +
    "        step(\"Render\")\n        capture_terminal_grid(snapshot)\n" +
    "        expect(grid_ok(snapshot)).to_equal(true)\n")
expect(tui_facts.capture_count).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/sspec_maintain/scoring_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSpec maintenance scoring.
- SSpec maintenance scoring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7acd2e99412ab57b023afbd3a61bf615aa291cd0eb2439f4f2f81baa329dc68c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7acd2e99412ab57b023afbd3a61bf615aa291cd0eb2439f4f2f81baa329dc68c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7acd2e99412ab57b023afbd3a61bf615aa291cd0eb2439f4f2f81baa329dc68c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/app/sspec_maintain/scoring_spec.spl
mirror: doc/06_spec/01_unit/app/sspec_maintain/scoring_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=55 coverage=100 maintainability=100
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/sspec_maintain/scoring_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
test/01_unit/app/sspec_maintain/scoring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/sspec_maintain/scoring_spec.spl:10:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'caps blockers and explains deductions across weak dimensions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sspec_maintain/scoring_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'awards all seven dimensions only to professional structural facts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/sspec_maintain/scoring_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an arithmetic tautology as a real oracle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

<!-- doc06-layout-migration: Historical generated/manual evidence retained; authoritative executable source remains at test/01_unit/app/sspec_maintain/scoring_spec.spl. -->

# Evidence Showcase Generation

> Verify the curated inventory, receipt-derived status model, generated-region

<!-- sdn-diagram:id=evidence_showcase_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=evidence_showcase_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

evidence_showcase_spec -> std
evidence_showcase_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=evidence_showcase_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Evidence Showcase Generation

Verify the curated inventory, receipt-derived status model, generated-region

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | REQ-EVS-001, REQ-EVS-002, REQ-EVS-003, REQ-EVS-004, |
| Category | Testing infrastructure |
| Status | Implemented |
| Plan | doc/03_plan/sys_test/evidence_showcase.md |
| Design | doc/05_design/evidence_showcase.md |
| Research | doc/01_research/local/evidence_showcase.md |
| Source | `test/03_system/app/testing/feature/evidence_showcase_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose

Verify the curated inventory, receipt-derived status model, generated-region
contract, discoverability, and modern SSpec operator flow without promoting
missing manifests to live evidence.

## Scenarios

### project evidence showcase

#### renders every critical inventory row without hand-authored truth

- Capture the feature evidence
- Verify the structured evidence
   - Expected: inventory.hubs.len() equals `4`
   - Expected: inventory.rows.len() equals `9`
   - Expected: critical_count equals `9`
   - Expected: rows.len() equals `9`
- Render the evidence for review
- Publish the showcase link


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val config = read_required("config/evidence_showcase.sdn")
val parsed = parse_evidence_showcase_inventory(config)
step("Verify the structured evidence")
match parsed:
    case Err(error):
        fail("showcase inventory rejected: " + error)
    case Ok(inventory):
        expect(inventory.hubs.len()).to_equal(4)
        expect(inventory.rows.len()).to_equal(9)
        var critical_count = 0
        for row in inventory.rows:
            if row.critical:
                critical_count = critical_count + 1
        expect(critical_count).to_equal(9)
        match resolve_evidence_showcase_inventory(inventory):
            case Err(error):
                fail("showcase evidence resolution failed: " + error)
            case Ok(rows):
                expect(rows.len()).to_equal(9)
                step("Render the evidence for review")
                val markdown = render_evidence_showcase_generated(
                    rows, "root"
                )
                expect(markdown).to_contain(
                    "## Generated evidence status"
                )
                expect(markdown).to_contain(
                    "## Critical capabilities"
                )
                expect(markdown).to_contain("`contract-only`")
                expect(markdown).to_contain("`planned`")
                step("Publish the showcase link")
                expect(read_required("FILE.md")).to_contain(
                    "`EVIDENCE_SHOWCASE.md`"
                )
                expect(read_required("README.md")).to_contain(
                    "[Evidence Showcase](EVIDENCE_SHOWCASE.md)"
                )
```

</details>

#### keeps one generated region in every showcase hub

- Capture the feature evidence
- Verify the structured evidence
   - Expected: start_count equals `5`
   - Expected: end_count equals `5`
- Render the evidence for review
   - Expected: paths.len() equals `5`
- Publish the showcase link


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Capture the feature evidence")
val paths = [
    "EVIDENCE_SHOWCASE.md",
    "src/os/EVIDENCE_SHOWCASE.md",
    "src/app/ide/EVIDENCE_SHOWCASE.md",
    "src/app/llm_caret/EVIDENCE_SHOWCASE.md",
    "src/lib/gc_async_mut/gpu/EVIDENCE_SHOWCASE.md"
]
step("Verify the structured evidence")
var start_count = 0
var end_count = 0
for path in paths:
    val content = read_required(path)
    start_count = start_count + content.split(
        "<!-- evidence-showcase:generated:start -->"
    ).len() - 1
    end_count = end_count + content.split(
        "<!-- evidence-showcase:generated:end -->"
    ).len() - 1
expect(start_count).to_equal(5)
expect(end_count).to_equal(5)
step("Render the evidence for review")
expect(paths.len()).to_equal(5)
step("Publish the showcase link")
expect(read_required("EVIDENCE_SHOWCASE.md")).to_contain(
    "Status is derived from validated manifests"
)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/evidence_showcase.md](doc/03_plan/sys_test/evidence_showcase.md)
- **Design:** [doc/05_design/evidence_showcase.md](doc/05_design/evidence_showcase.md)
- **Research:** [doc/01_research/local/evidence_showcase.md](doc/01_research/local/evidence_showcase.md)


</details>

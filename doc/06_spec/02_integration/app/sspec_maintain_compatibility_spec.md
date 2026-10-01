# Sspec Maintain Compatibility Specification

> Tests covering SSpec maintenance compatibility.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sspec Maintain Compatibility Specification

## Scenarios

### SSpec maintenance compatibility

#### keeps spipe-docgen help available beside maintenance help

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps spipe-docgen help available beside maintenance help
   - Expected: spipe_status equals `0`
   - Expected: spipe_error.trim() equals ``
   - Expected: maintenance_status equals `0`
   - Expected: maintenance_error.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-010
step("keeps spipe-docgen help available beside maintenance help")
val binary = _compatibility_simple_binary()
val (spipe_help, spipe_error, spipe_status) = process_run(binary,
    ["spipe-docgen", "--help"])
expect(spipe_status).to_equal(0)
expect(spipe_help.lower()).to_contain("spipe")
expect(spipe_error.trim()).to_equal("")
val (maintenance_help, maintenance_error, maintenance_status) =
    process_run(binary, ["sspec-maintain", "--help"])
expect(maintenance_status).to_equal(0)
expect(maintenance_help).to_contain("spipe-docgen")
expect(maintenance_help).to_contain("spec-gen is legacy")
expect(maintenance_error.trim()).to_equal("")
```

</details>

#### preserves canonical spipe-docgen generation in an isolated output tree

- preserves canonical spipe-docgen generation in an isolated output tree
- preserves canonical spipe-docgen generation in an isolated output tree
   - Expected: run_spipe_docgen([source_path, "--output", output_path]) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("preserves canonical spipe-docgen generation in an isolated output tree")
step("preserves canonical spipe-docgen generation in an isolated output tree")
val root = "/tmp/sspec_maintain_spipe_compatibility"
val source_path = root + "/test/compatibility_spec.spl"
val output_path = root + "/doc/06_spec"
dir_remove(root, true)
expect(dir_create_all(root + "/test")).to_be(true)
expect(file_atomic_write(source_path,
    _compatibility_spec_source())).to_be(true)
expect(run_spipe_docgen([source_path, "--output", output_path])).to_equal(0)
expect(_contains_markdown(dir_walk(output_path))).to_be(true)
dir_remove(root, true)
```

</details>

#### routes public documentize through isolated canonical SPipe staging

- routes public documentize through isolated canonical SPipe staging
- routes public documentize through isolated canonical SPipe staging


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes public documentize through isolated canonical SPipe staging")
step("routes public documentize through isolated canonical SPipe staging")
val root = "/tmp/sspec_maintain_documentize_compatibility"
val source_path = root + "/test/compatibility_spec.spl"
val output_path = root + "/compatibility_manual.md"
dir_remove(root, true)
expect(dir_create_all(root + "/test")).to_be(true)
expect(file_atomic_write(source_path,
    _compatibility_spec_source())).to_be(true)
expect(run_sspec_maintain(["documentize", source_path, "--output",
    output_path])).to_equal(0)
val manual = file_read(output_path) ?? ""
expect(manual).to_contain("## Generation history")
expect(manual).to_contain("## SSpec documentization scorecard")
expect(manual).to_contain("Source SHA-256:")
dir_remove(root, true)
```

</details>

#### keeps public directory JSON byte deterministic in normalized path order

- keeps public directory JSON byte deterministic in normalized path order
- keeps public directory JSON byte deterministic in normalized path order
   - Expected: first_status equals `0`
   - Expected: second_status equals `0`
   - Expected: second equals `first`
   - Expected: first_error.trim() equals ``
   - Expected: second_error.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("keeps public directory JSON byte deterministic in normalized path order")
step("keeps public directory JSON byte deterministic in normalized path order")
val root = "/tmp/sspec_maintain_directory_order"
dir_remove(root, true)
expect(dir_create_all(root)).to_be(true)
expect(file_atomic_write(root + "/z_spec.spl",
    _compatibility_spec_source())).to_be(true)
expect(file_atomic_write(root + "/a_spec.spl",
    _compatibility_spec_source())).to_be(true)
val binary = _compatibility_simple_binary()
val (first, first_error, first_status) = process_run(binary,
    ["sspec-maintain", "scan", root, "--no-cache", "--format", "json"])
val (second, second_error, second_status) = process_run(binary,
    ["sspec-maintain", "scan", root, "--no-cache", "--format", "json"])
expect(first_status).to_equal(0)
expect(second_status).to_equal(0)
expect(second).to_equal(first)
expect(first.find("a_spec.spl")).to_be_less_than(first.find("z_spec.spl"))
expect(first_error.trim()).to_equal("")
expect(second_error.trim()).to_equal("")
dir_remove(root, true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/sspec_maintain_compatibility_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSpec maintenance compatibility.
- SSpec maintenance compatibility

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
- `REQ-SSDOC-010\n"`
- `REQ-SSDOC-010`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1cfcacc4236eeb2e7e78e4d496cc18f75c6bb676b011900ab7f4f21f7ff75abf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1cfcacc4236eeb2e7e78e4d496cc18f75c6bb676b011900ab7f4f21f7ff75abf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1cfcacc4236eeb2e7e78e4d496cc18f75c6bb676b011900ab7f4f21f7ff75abf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/02_integration/app/sspec_maintain_compatibility_spec.spl
mirror: doc/06_spec/02_integration/app/sspec_maintain_compatibility_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/02_integration/app/sspec_maintain_compatibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/sspec_maintain_compatibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/sspec_maintain_compatibility_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/sspec_maintain_compatibility_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/02_integration/app/sspec_maintain_compatibility_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps spipe-docgen help available beside maintenance help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/sspec_maintain_compatibility_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves canonical spipe-docgen generation in an isolated output tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/sspec_maintain_compatibility_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes public documentize through isolated canonical SPipe staging' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

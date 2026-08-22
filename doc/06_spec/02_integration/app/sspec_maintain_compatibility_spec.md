# sspec_maintain_compatibility_spec

> Verifies the sspec maintain compatibility behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sspec_maintain_compatibility_spec

Verifies the sspec maintain compatibility behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/02_integration/app/sspec_maintain_compatibility_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the sspec maintain compatibility behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### SSpec maintenance compatibility

#### keeps spipe-docgen help available beside maintenance help

- Verify: keeps spipe-docgen help available beside maintenance help
- keeps spipe-docgen help available beside maintenance help
   - Expected: spipe_status equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: spipe_error.trim() equals ``
   - Expected: maintenance_status equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: maintenance_error.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-010\n
step("Verify: keeps spipe-docgen help available beside maintenance help")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# @req: REQ-SSDOC-010
step("keeps spipe-docgen help available beside maintenance help")
val binary = _compatibility_simple_binary()
val (spipe_help, spipe_error, spipe_status) = process_run(binary,
    ["spipe-docgen", "--help"])
expect(spipe_status).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(spipe_help.lower()).to_contain("spipe")
expect(spipe_error.trim()).to_equal("")
val (maintenance_help, maintenance_error, maintenance_status) =
    process_run(binary, ["sspec-maintain", "--help"])
expect(maintenance_status).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(maintenance_help).to_contain("spipe-docgen")
expect(maintenance_help).to_contain("spec-gen is legacy")
expect(maintenance_error.trim()).to_equal("")
```

</details>

#### preserves canonical spipe-docgen generation in an isolated output tree

- Verify: preserves canonical spipe-docgen generation in an isolated output tree
- preserves canonical spipe-docgen generation in an isolated output tree
   - Expected: run_spipe_docgen([source_path, "--output", output_path]) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-010\n
# @req: REQ-SSDOC-010
step("Verify: preserves canonical spipe-docgen generation in an isolated output tree")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("preserves canonical spipe-docgen generation in an isolated output tree")
val root = "/tmp/sspec_maintain_spipe_compatibility"
val source_path = root + "/test/compatibility_spec.spl"
val output_path = root + "/doc/06_spec"
dir_remove(root, true)
expect(dir_create_all(root + "/test")).to_be(true)
expect(file_atomic_write(source_path,
    _compatibility_spec_source())).to_be(true)
expect(run_spipe_docgen([source_path, "--output", output_path])).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(_contains_markdown(dir_walk(output_path))).to_be(true)
dir_remove(root, true)
```

</details>

#### routes public documentize through isolated canonical SPipe staging

- Verify: routes public documentize through isolated canonical SPipe staging
- routes public documentize through isolated canonical SPipe staging


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-010\n
# @req: REQ-SSDOC-010
step("Verify: routes public documentize through isolated canonical SPipe staging")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
step("routes public documentize through isolated canonical SPipe staging")
val root = "/tmp/sspec_maintain_documentize_compatibility"
val source_path = root + "/test/compatibility_spec.spl"
val output_path = root + "/compatibility_manual.md"
dir_remove(root, true)
expect(dir_create_all(root + "/test")).to_be(true)
expect(file_atomic_write(source_path,
    _compatibility_spec_source())).to_be(true)
expect(run_sspec_maintain(["documentize", source_path, "--output",
    output_path])).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
val manual = file_read(output_path) ?? ""
expect(manual).to_contain("## Generation history")
expect(manual).to_contain("## SSpec documentization scorecard")
expect(manual).to_contain("Source SHA-256:")
dir_remove(root, true)
```

</details>

#### keeps public directory JSON byte deterministic in normalized path order

- Verify: keeps public directory JSON byte deterministic in normalized path order
- keeps public directory JSON byte deterministic in normalized path order
   - Expected: first_status equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: second_status equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: second equals `first`
   - Expected: first_error.trim() equals ``
   - Expected: second_error.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSDOC-010\n
# @req: REQ-SSDOC-010
step("Verify: keeps public directory JSON byte deterministic in normalized path order")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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
expect(first_status).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(second_status).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(second).to_equal(first)
expect(first.find("a_spec.spl")).to_be_less_than(first.find("z_spec.spl"))
expect(first_error.trim()).to_equal("")
expect(second_error.trim()).to_equal("")
dir_remove(root, true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `578f04c437866c7b43e13c806441526f4b78dd3a9276722191023a05f647f52c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `578f04c437866c7b43e13c806441526f4b78dd3a9276722191023a05f647f52c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `578f04c437866c7b43e13c806441526f4b78dd3a9276722191023a05f647f52c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/app/sspec_maintain_compatibility_spec.spl
mirror: doc/06_spec/02_integration/app/sspec_maintain_compatibility_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/sspec_maintain_compatibility_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/app/sspec_maintain_compatibility_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/sspec_maintain_compatibility_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

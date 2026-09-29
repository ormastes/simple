# gpu_tutorial_curriculum_acceptance_spec

> Purpose: prove the CUDA curriculum under examples/08_gpu/simple_cuda_example

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_tutorial_curriculum_acceptance_spec

Purpose: prove the CUDA curriculum under examples/08_gpu/simple_cuda_example

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Purpose: prove the CUDA curriculum under examples/08_gpu/simple_cuda_example
    still teaches what it claims to. Every module must be documented, every
    document must carry runnable examples, every runnable example must be
    covered by a spec, and no tier may quietly lose a chapter.

    Audience: whoever maintains the GPU tutorial and anyone learning from it.
    Nothing here touches a GPU -- these checks are pure filesystem reads and run
    identically on a machine with no device at all.

    Run: bin/simple test test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl

## Scenarios

### The CUDA tutorial is a teaching artefact, not a folder of prose

#### gives every module of the curriculum a README a learner can open

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Every chapter is documented (expected show, folded, detail, or skip)


- SKIP: the tutorial submodule is not checked out at {TUTORIAL_ROOT} -- reported explicitly rather than passing silently
- Walk every module the workbook promises and open its README
- Confirm not one chapter is left undocumented
   - Expected: missing equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-008
# @req REQ-GPU-PORT-012
if not tutorial_present():
    step("SKIP: the tutorial submodule is not checked out at {TUTORIAL_ROOT} -- reported explicitly rather than passing silently")
    skip("tutorial submodule absent: {TUTORIAL_ROOT}")
else:
    step("Walk every module the workbook promises and open its README")
    var missing = 0
    for module in expected_modules():
        if not file_exists("{TUTORIAL_ROOT}/{module}/README.md"):
            print("MISSING README: {module}")
            missing = missing + 1

    step("Confirm not one chapter is left undocumented")
    expect(missing).to_equal(0)
```

</details>

#### backs every README with at least one runnable sdoctest, so the teaching text fails when it goes stale

- SKIP: the tutorial submodule is not checked out at {TUTORIAL_ROOT}
- Read each module README and look for an executable sdoctest fence
- Confirm the scan was not vacuous -- a zero-file run must never read as a pass
   - Expected: checked equals `expected_modules().len()`
- Confirm every chapter's documentation is fail-closed rather than untested prose
   - Expected: proseonly equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-009
# @req REQ-GPU-PORT-012
if not tutorial_present():
    step("SKIP: the tutorial submodule is not checked out at {TUTORIAL_ROOT}")
    skip("tutorial submodule absent: {TUTORIAL_ROOT}")
else:
    step("Read each module README and look for an executable sdoctest fence")
    var proseonly = 0
    var checked = 0
    for module in expected_modules():
        val path = "{TUTORIAL_ROOT}/{module}/README.md"
        if file_exists(path):
            checked = checked + 1
            val body = read_file_text(path)
            if not body.contains("```sdoctest"):
                print("NO SDOCTEST FENCE: {module}")
                proseonly = proseonly + 1

    step("Confirm the scan was not vacuous -- a zero-file run must never read as a pass")
    expect(checked).to_equal(expected_modules().len())

    step("Confirm every chapter's documentation is fail-closed rather than untested prose")
    expect(proseonly).to_equal(0)
```

</details>

#### ships a spec alongside every module that ships a runnable program

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section Every runnable example is a tested example (expected show, folded, detail, or skip)


- SKIP: the tutorial submodule is not checked out at {TUTORIAL_ROOT}
- Find every module that offers a learner a main.spl to run
- Confirm the curriculum actually contains runnable programs
- Confirm not one runnable example is shipped without a spec covering it
   - Expected: uncovered equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-010
# @req REQ-GPU-PORT-012
if not tutorial_present():
    step("SKIP: the tutorial submodule is not checked out at {TUTORIAL_ROOT}")
    skip("tutorial submodule absent: {TUTORIAL_ROOT}")
else:
    step("Find every module that offers a learner a main.spl to run")
    var runnable = 0
    var uncovered = 0
    for module in expected_modules():
        if file_exists("{TUTORIAL_ROOT}/{module}/main.spl"):
            runnable = runnable + 1
            if not file_exists("{TUTORIAL_ROOT}/{module}/spec.spl"):
                print("RUNNABLE BUT UNCOVERED: {module}")
                uncovered = uncovered + 1

    step("Confirm the curriculum actually contains runnable programs")
    expect(runnable).to_be_greater_than(0)

    step("Confirm not one runnable example is shipped without a spec covering it")
    expect(uncovered).to_equal(0)
```

</details>

#### still covers all six tiers of the workbook, so a dropped module fails this spec

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section No tier loses a chapter (expected show, folded, detail, or skip)


- SKIP: the tutorial submodule is not checked out at {TUTORIAL_ROOT}
- Confirm every tier directory of the curriculum is present
- Confirm the expected module set 11..19, 21..27, 31..38, 61..66, 71..73, 81..82 is complete
   - Expected: present equals `33`
   - Expected: present equals `expected_modules().len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-GPU-PORT-011
# @req REQ-GPU-PORT-012
if not tutorial_present():
    step("SKIP: the tutorial submodule is not checked out at {TUTORIAL_ROOT}")
    skip("tutorial submodule absent: {TUTORIAL_ROOT}")
else:
    step("Confirm every tier directory of the curriculum is present")
    for tier in ["10.cuda_basic", "20.cuda_intermediate", "30.cuda_libraries",
                 "60.llm_implementation", "70.gpu_optimization", "80.transformer"]:
        assert_true(file_exists("{TUTORIAL_ROOT}/{tier}"))

    step("Confirm the expected module set 11..19, 21..27, 31..38, 61..66, 71..73, 81..82 is complete")
    var present = 0
    for module in expected_modules():
        if file_exists("{TUTORIAL_ROOT}/{module}"):
            present = present + 1
        else:
            print("DROPPED MODULE: {module}")
    expect(present).to_equal(33)
    expect(present).to_equal(expected_modules().len())
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-GPU-PORT-008`
- `REQ-GPU-PORT-012`
- `REQ-GPU-PORT-009`
- `REQ-GPU-PORT-010`
- `REQ-GPU-PORT-011`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bfb61608ac17f0719c8c2fccbba65296a32315408abaa008379e1bdee06f08b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bfb61608ac17f0719c8c2fccbba65296a32315408abaa008379e1bdee06f08b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bfb61608ac17f0719c8c2fccbba65296a32315408abaa008379e1bdee06f08b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl
mirror: doc/06_spec/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives every module of the curriculum a README a learner can open' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'backs every README with at least one runnable sdoctest, so the teaching text fails when it goes stale' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/acceptance/gpu_tutorial_curriculum_acceptance_spec.spl:115:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ships a spec alongside every module that ships a runnable program' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

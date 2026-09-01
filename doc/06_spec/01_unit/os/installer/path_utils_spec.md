# Path Utils Specification

> Tests covering path_utils.parent_dir_chain.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Path Utils Specification

## Scenarios

### path_utils.parent_dir_chain

#### returns nested intermediate directories under the root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns nested intermediate directories under the root
   - Expected: chain.len() equals `2`
   - Expected: chain[0] equals `/mnt/target/etc`
   - Expected: chain[1] equals `/mnt/target/etc/pkg`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns nested intermediate directories under the root")
val chain = parent_dir_chain("/mnt/target", "/etc/pkg/registry.sdn")
expect(chain.len()).to_equal(2)
expect(chain[0]).to_equal("/mnt/target/etc")
expect(chain[1]).to_equal("/mnt/target/etc/pkg")
```

</details>

#### returns a single directory for a one-level file path

- returns a single directory for a one-level file path
   - Expected: chain.len() equals `1`
   - Expected: chain[0] equals `/mnt/target/SYS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns a single directory for a one-level file path")
val chain = parent_dir_chain("/mnt/target", "/SYS/LLVMMAN.TXT")
expect(chain.len()).to_equal(1)
expect(chain[0]).to_equal("/mnt/target/SYS")
```

</details>

#### returns an empty chain for a root-level file

- returns an empty chain for a root-level file
   - Expected: chain.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns an empty chain for a root-level file")
val chain = parent_dir_chain("/mnt/target", "/README")
expect(chain.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/installer/path_utils_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering path_utils.parent_dir_chain.
- path_utils.parent_dir_chain

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c409370ddc99269b0012575b058a8b88955b9ed618460aea18adbdc1c411100f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c409370ddc99269b0012575b058a8b88955b9ed618460aea18adbdc1c411100f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c409370ddc99269b0012575b058a8b88955b9ed618460aea18adbdc1c411100f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/installer/path_utils_spec.spl
mirror: doc/06_spec/01_unit/os/installer/path_utils_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/installer/path_utils_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/installer/path_utils_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/installer/path_utils_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/installer/path_utils_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns nested intermediate directories under the root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/path_utils_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a single directory for a one-level file path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/path_utils_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an empty chain for a root-level file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

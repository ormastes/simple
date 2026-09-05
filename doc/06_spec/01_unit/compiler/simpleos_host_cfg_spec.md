# Simpleos Host Cfg Specification

> Tests covering SimpleOS host-OS cfg recognition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Host Cfg Specification

## Scenarios

### SimpleOS host-OS cfg recognition

#### cfg_normalize_os normalizes 'simpleos' to 'simpleos'

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- cfg_normalize_os normalizes 'simpleos' to 'simpleos'
   - Expected: cfg_normalize_os("simpleos") equals `simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cfg_normalize_os normalizes 'simpleos' to 'simpleos'")
expect(cfg_normalize_os("simpleos")).to_equal("simpleos")
```

</details>

#### cfg_normalize_os normalizes 'SimpleOS' to 'simpleos'

- cfg_normalize_os normalizes 'SimpleOS' to 'simpleos'
   - Expected: cfg_normalize_os("SimpleOS") equals `simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cfg_normalize_os normalizes 'SimpleOS' to 'simpleos'")
expect(cfg_normalize_os("SimpleOS")).to_equal("simpleos")
```

</details>

#### cfg_normalize_os regression: linux still normalizes to 'linux'

- cfg_normalize_os regression: linux still normalizes to 'linux'
   - Expected: cfg_normalize_os("linux") equals `linux`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cfg_normalize_os regression: linux still normalizes to 'linux'")
expect(cfg_normalize_os("linux")).to_equal("linux")
```

</details>

#### cfg_normalize_os regression: freebsd still normalizes to 'freebsd'

- cfg_normalize_os regression: freebsd still normalizes to 'freebsd'
   - Expected: cfg_normalize_os("freebsd") equals `freebsd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cfg_normalize_os regression: freebsd still normalizes to 'freebsd'")
expect(cfg_normalize_os("freebsd")).to_equal("freebsd")
```

</details>

#### PlatformAttrValue.create marks os=simpleos as valid

- PlatformAttrValue.create marks os=simpleos as valid
   - Expected: result.is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("PlatformAttrValue.create marks os=simpleos as valid")
val result = PlatformAttrValue.create("os", "simpleos")
expect(result.is_valid).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/simpleos_host_cfg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS host-OS cfg recognition.
- SimpleOS host-OS cfg recognition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a0097447a51324e217ed18f433cf38b332124417d405d4f2da8e68fe4d4a694b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a0097447a51324e217ed18f433cf38b332124417d405d4f2da8e68fe4d4a694b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a0097447a51324e217ed18f433cf38b332124417d405d4f2da8e68fe4d4a694b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/simpleos_host_cfg_spec.spl
mirror: doc/06_spec/01_unit/compiler/simpleos_host_cfg_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/simpleos_host_cfg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/simpleos_host_cfg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/simpleos_host_cfg_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cfg_normalize_os normalizes 'simpleos' to 'simpleos'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/simpleos_host_cfg_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cfg_normalize_os normalizes 'SimpleOS' to 'simpleos'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/simpleos_host_cfg_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'cfg_normalize_os regression: linux still normalizes to 'linux'' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

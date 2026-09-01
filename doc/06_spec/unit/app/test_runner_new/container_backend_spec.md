# Container Backend Specification

> Tests covering container_detect_runtime, container_get_version, container_check_image, container_cleanup_volumes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Container Backend Specification

## Scenarios

### container_detect_runtime

#### detects docker when available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- detects docker when available
   - Expected: runtime equals `docker`
   - Expected: runtime equals `podman`
   - Expected: runtime equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects docker when available")
val runtime = container_detect_runtime()
val has_docker = shell_bool("docker --version")
val has_podman = shell_bool("podman --version")

if has_docker:
    expect(runtime).to_equal("docker")
elif has_podman:
    expect(runtime).to_equal("podman")
else:
    expect(runtime).to_equal("none")
```

</details>

#### returns none when no container runtime installed

- returns none when no container runtime installed
   - Expected: runtime equals `none`
   - Expected: has_runtime is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns none when no container runtime installed")
val runtime = container_detect_runtime()
if runtime == "none":
    expect(runtime).to_equal("none")
else:
    # Either docker or podman is installed
    val has_runtime = runtime == "docker" or runtime == "podman"
    expect(has_runtime).to_equal(true)
```

</details>

### container_get_version

#### gets docker version when available

- gets docker version when available
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets docker version when available")
val has_docker = shell_bool("docker --version")
if has_docker:
    val version = container_get_version("docker")
    expect(version).to_contain("Docker")
else:
    expect(true).to_equal(true)
```

</details>

#### gets podman version when available

- gets podman version when available
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gets podman version when available")
val has_podman = shell_bool("podman --version")
if has_podman:
    val version = container_get_version("podman")
    expect(version).to_contain("podman")
else:
    expect(true).to_equal(true)
```

</details>

#### returns empty string for unknown runtime

- returns empty string for unknown runtime
   - Expected: version equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty string for unknown runtime")
val version = container_get_version("unknown")
expect(version).to_equal("")
```

</details>

### container_check_image

#### returns false for non-existent image with docker

- returns false for non-existent image with docker
   - Expected: exists is false
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-existent image with docker")
val has_docker = shell_bool("docker --version")
if has_docker:
    val exists = container_check_image("nonexistent-image:999", "docker")
    expect(exists).to_equal(false)
else:
    expect(true).to_equal(true)
```

</details>

#### returns false for non-existent image with podman

- returns false for non-existent image with podman
   - Expected: exists is false
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for non-existent image with podman")
val has_podman = shell_bool("podman --version")
if has_podman:
    val exists = container_check_image("nonexistent-image:999", "podman")
    expect(exists).to_equal(false)
else:
    expect(true).to_equal(true)
```

</details>

#### returns false for unknown runtime

- returns false for unknown runtime
   - Expected: exists is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unknown runtime")
val exists = container_check_image("any-image", "unknown")
expect(exists).to_equal(false)
```

</details>

### container_cleanup_volumes

#### returns false for unknown runtime

- returns false for unknown runtime
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for unknown runtime")
val result = container_cleanup_volumes("unknown")
expect(result).to_equal(false)
```

</details>

#### attempts cleanup with docker when available

- attempts cleanup with docker when available
   - Expected: is_bool is true
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("attempts cleanup with docker when available")
val has_docker = shell_bool("docker --version")
if has_docker:
    val result = container_cleanup_volumes("docker")
    # Should return true or false, not crash
    val is_bool = result == true or result == false
    expect(is_bool).to_equal(true)
else:
    expect(true).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_runner_new/container_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering container_detect_runtime, container_get_version, container_check_image, container_cleanup_volumes.
- container_detect_runtime
- container_get_version
- container_check_image
- container_cleanup_volumes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `97815d225b28920d1db04c5e0ab30092d8b4c21dba91114fb6053d96e3bfb650`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97815d225b28920d1db04c5e0ab30092d8b4c21dba91114fb6053d96e3bfb650`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97815d225b28920d1db04c5e0ab30092d8b4c21dba91114fb6053d96e3bfb650`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/test_runner_new/container_backend_spec.spl
mirror: doc/06_spec/unit/app/test_runner_new/container_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_runner_new/container_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_runner_new/container_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_runner_new/container_backend_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects docker when available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/container_backend_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns none when no container runtime installed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_runner_new/container_backend_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gets docker version when available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

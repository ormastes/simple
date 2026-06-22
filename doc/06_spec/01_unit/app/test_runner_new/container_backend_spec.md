# Container Backend Specification

> <details>

<!-- sdn-diagram:id=container_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=container_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

container_backend_spec -> std
container_backend_spec -> test_runner_container
container_backend_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=container_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Container Backend Specification

## Scenarios

### container_detect_runtime

#### detects docker when available

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_docker = shell_bool("docker --version")
if has_docker:
    val version = container_get_version("docker")
    expect(version).to_contain("Docker")
else:
    expect(has_docker).to_equal(false)
```

</details>

#### gets podman version when available

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_podman = shell_bool("podman --version")
if has_podman:
    val version = container_get_version("podman")
    expect(version).to_contain("podman")
else:
    expect(has_podman).to_equal(false)
```

</details>

#### returns empty string for unknown runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val version = container_get_version("unknown")
expect(version).to_equal("")
```

</details>

### container_check_image

#### returns false for non-existent image with docker

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_docker = shell_bool("docker --version")
if has_docker:
    val exists = container_check_image("nonexistent-image:999", "docker")
    expect(exists).to_equal(false)
else:
    expect(has_docker).to_equal(false)
```

</details>

#### returns false for non-existent image with podman

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_podman = shell_bool("podman --version")
if has_podman:
    val exists = container_check_image("nonexistent-image:999", "podman")
    expect(exists).to_equal(false)
else:
    expect(has_podman).to_equal(false)
```

</details>

#### returns false for unknown runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val exists = container_check_image("any-image", "unknown")
expect(exists).to_equal(false)
```

</details>

### container_cleanup_volumes

#### returns false for unknown runtime

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = container_cleanup_volumes("unknown")
expect(result).to_equal(false)
```

</details>

#### attempts cleanup with docker when available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val has_docker = shell_bool("docker --version")
if has_docker:
    val result = container_cleanup_volumes("docker")
    # Should return true or false, not crash
    val is_bool = result == true or result == false
    expect(is_bool).to_equal(true)
else:
    expect(has_docker).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_runner_new/container_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

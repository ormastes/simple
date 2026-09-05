# macOS GPU Compiler Admission Behavioral Contract

> Exercises the shared classifier and the public V3 manifest admission surface with deterministic temporary artifacts. The public fixture substitutes only the already-completed manifest verifier subprocess; all compiler canonicality, mode, digest, and output-population checks run through the production admission library.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# macOS GPU Compiler Admission Behavioral Contract

Exercises the shared classifier and the public V3 manifest admission surface with deterministic temporary artifacts. The public fixture substitutes only the already-completed manifest verifier subprocess; all compiler canonicality, mode, digest, and output-population checks run through the production admission library.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | `doc/03_plan/agent_tasks/macos_vulkan_metal_host_qemu_rendering_completion.md` |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/check/macos_gpu_compiler_admission_behavior_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Exercises the shared classifier and the public V3 manifest admission surface
with deterministic temporary artifacts. The public fixture substitutes only
the already-completed manifest verifier subprocess; all compiler canonicality,
mode, digest, and output-population checks run through the production admission
library.

The contract is fail-closed: a compiler is accepted only when its path, file
mode, digest, printable-content inspection, manifest identity, and source kind
all agree with the canonical Stage-3 producer.

## Examples

Run this specification through the self-hosted runtime:

`SIMPLE_LIB=src <pure-simple-runtime> test
test/03_system/check/macos_gpu_compiler_admission_behavior_spec.spl
--mode=interpreter`

Each scenario delegates to the deterministic shell fixture and requires both a
zero fixture exit code and its explicit pass marker. Rejection scenarios pass
only when the production admission function rejects the constructed artifact.

## Acceptance

- Ordinary compiler content and generic debug prose are accepted.
- The exact Rust bootstrap-seed banner is rejected.
- `compiler_rust`, `target/debug`, and terminal `debug/simple` paths are
  rejected.
- A failing `strings` command rejects instead of silently accepting.
- Public V3 admission rejects symlinked and non-executable compilers.
- Successful public V3 admission publishes compiler identity from the one
  `build_compiler_identity` manifest field.
- A compiler mutation during printable-content inspection is rejected by the
  post-inspection digest check.

## Scenarios

### macOS GPU compiler admission

#### accepts ordinary compiler content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("classifier-ordinary")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### accepts generic debug prose without treating it as provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("classifier-debug-prose")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects the exact Rust bootstrap seed banner

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("classifier-rust-seed-banner")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects compiler_rust path variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("classifier-compiler-rust-path")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects target debug path variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("classifier-target-debug-path")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects terminal debug simple path variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("classifier-debug-simple-path")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects when strings cannot inspect the compiler

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("classifier-strings-failure")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### populates the singular compiler identity through public V3 admission

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("public-regular-identity")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects a symlinked compiler through public V3 admission

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("public-symlink")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects a non-executable compiler through public V3 admission

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("public-non-executable")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects a wrong compiler identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("public-wrong-identity")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects a wrong compiler source kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("public-wrong-source-kind")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects a missing compiler identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("public-missing-identity")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects a duplicate compiler identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("public-duplicate-identity")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

#### rejects compiler mutation during printable-content inspection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _stderr, code) = run_fixture("public-mutation-during-classifier")
expect(code).to_equal(0)
expect(stdout).to_contain("macos_gpu_compiler_admission_fixture_status=pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** N/A
- **Plan:** `doc/03_plan/agent_tasks/macos_vulkan_metal_host_qemu_rendering_completion.md`
- **Design:** N/A
- **Research:** N/A


</details>

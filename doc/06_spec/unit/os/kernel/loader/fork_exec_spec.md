# fork_exec_spec

> Fork/Exec Structural Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# fork_exec_spec

Fork/Exec Structural Specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/loader/fork_exec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Fork/Exec Structural Specification

Tests the kernel-level exec (syscall 59) dispatch path structurally.
These specs verify:
  - exec rejects invalid arguments (empty path)
  - exec resolves executable bytes from synthetic sources
  - The resolution pipeline returns correct bytes end-to-end

No actual processes are spawned — all tests exercise the structural
contract of the executable resolution path.

Run:
  bin/simple test test/unit/os/kernel/loader/fork_exec_spec.spl

## Scenarios

### exec — argument validation

#### exec rejects empty path with EINVAL

- exec rejects empty path with EINVAL
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap().starts_with("EINVAL") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exec rejects empty path with EINVAL")
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
val result = resolve_executable_bytes("", Architecture.X86_64)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap().starts_with("EINVAL")).to_equal(true)
```

</details>

#### exec rejects nonexistent path with ENOENT

- exec rejects nonexistent path with ENOENT
   - Expected: result.is_err() is true
   - Expected: result.err().unwrap().starts_with("ENOENT") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exec rejects nonexistent path with ENOENT")
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
# Non-absolute path avoids VFS reader (interpreter limitation)
val result = resolve_executable_bytes("no_such_binary", Architecture.X86_64)
expect(result.is_err()).to_equal(true)
expect(result.err().unwrap().starts_with("ENOENT")).to_equal(true)
```

</details>

### exec — image replacement structural
_Verify exec can load and parse a new image to replace the current one._

#### exec resolves synthetic bytes for a replacement image

- exec resolves synthetic bytes for a replacement image
   - Expected: bytes_result.is_ok() is true
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[1] equals `0x45.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exec resolves synthetic bytes for a replacement image")
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()

val payload = _elf_magic_payload()
_set_synthetic_initramfs_for_test("/sys/apps/new_image", payload)

# Step 1: resolve bytes (what exec does internally)
val bytes_result = resolve_executable_bytes("/sys/apps/new_image", Architecture.X86_64)
expect(bytes_result.is_ok()).to_equal(true)
val bytes = bytes_result.unwrap()
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[1]).to_equal(0x45.to_u8())

_clear_synthetic_initramfs_for_test()
```

</details>

#### exec resolves path bytes via resolve_executable_bytes_from_path_bytes

- exec resolves path bytes via resolve_executable_bytes_from_path_bytes
   - Expected: result.is_ok() is true
   - Expected: bytes[0] equals `0x7F.to_u8()`
   - Expected: bytes[1] equals `0x45.to_u8()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exec resolves path bytes via resolve_executable_bytes_from_path_bytes")
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()
app_registry_clear()
app_registry_register("/sys/apps/path_bytes_test", "PBTST.SMF", false)

val payload = _elf_magic_payload()
_set_synthetic_initramfs_for_test("/sys/apps/path_bytes_test", payload)

val path_bytes = rt_text_to_bytes("/sys/apps/path_bytes_test")
val result = resolve_executable_bytes_from_path_bytes(path_bytes, Architecture.X86_64)
expect(result.is_ok()).to_equal(true)
val bytes = result.unwrap()
expect(bytes[0]).to_equal(0x7F.to_u8())
expect(bytes[1]).to_equal(0x45.to_u8())

_clear_synthetic_initramfs_for_test()
```

</details>

### fork+exec lifecycle — structural
_Verify the complete fork+exec API surface compiles and the pipeline is coherent._

#### full lifecycle: resolve -> ELF bytes confirmed

- full lifecycle: resolve -> ELF bytes confirmed
   - Expected: bytes_result.is_ok() is true
   - Expected: raw_bytes[0] equals `0x7F.to_u8()`
   - Expected: raw_bytes[1] equals `0x45.to_u8()`
   - Expected: raw_bytes[2] equals `0x4C.to_u8()`
   - Expected: raw_bytes[3] equals `0x46.to_u8()`
   - Expected: raw_bytes.len() equals `elf_data.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full lifecycle: resolve -> ELF bytes confirmed")
_clear_synthetic_initramfs_for_test()
_clear_synthetic_vfs_for_test()

val elf_data = _minimal_elf64_x86_64()
_set_synthetic_initramfs_for_test("/sys/apps/lifecycle", elf_data)

# Parent would fork() (syscall 57) — returns child PID in parent.
# Child would exec() (syscall 59) — replaces its image.
# We test the exec resolution part structurally.

val bytes_result = resolve_executable_bytes("/sys/apps/lifecycle", Architecture.X86_64)
expect(bytes_result.is_ok()).to_equal(true)
val raw_bytes = bytes_result.unwrap()

# Verify resolved bytes are ELF
expect(raw_bytes[0]).to_equal(0x7F.to_u8())
expect(raw_bytes[1]).to_equal(0x45.to_u8())
expect(raw_bytes[2]).to_equal(0x4C.to_u8())
expect(raw_bytes[3]).to_equal(0x46.to_u8())

# Verify byte count matches
expect(raw_bytes.len()).to_equal(elf_data.len())

_clear_synthetic_initramfs_for_test()
```

</details>

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

- Canonical SPipe generation for source `acf287fa29c23da6116762372749c7fa329681cc53c427dff8d8f6a1fdf26357`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `acf287fa29c23da6116762372749c7fa329681cc53c427dff8d8f6a1fdf26357`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `acf287fa29c23da6116762372749c7fa329681cc53c427dff8d8f6a1fdf26357`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/loader/fork_exec_spec.spl
mirror: doc/06_spec/unit/os/kernel/loader/fork_exec_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/loader/fork_exec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/loader/fork_exec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/loader/fork_exec_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exec rejects empty path with EINVAL' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/fork_exec_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exec rejects nonexistent path with ENOENT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/loader/fork_exec_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exec resolves synthetic bytes for a replacement image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

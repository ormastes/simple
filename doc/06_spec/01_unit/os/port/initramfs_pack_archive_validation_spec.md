# Initramfs Pack Archive Validation Specification

> Tests covering SimpleOS initramfs archive role validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Initramfs Pack Archive Validation Specification

## Scenarios

### SimpleOS initramfs archive role validation

#### admits explicit target-native ELF and SMF init artifacts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- admits explicit target-native ELF and SMF init artifacts


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits explicit target-native ELF and SMF init artifacts")
expect(initramfs_init_artifact_admission(
    "build/os/simpleos-init", _elf_fixture(1u8)).is_ok()).to_equal(true)
expect(initramfs_init_artifact_admission(
    "build/os/simpleos-init.smf", _smf_fixture(1u8)).is_ok()).to_equal(true)
```

</details>

#### rejects absent, empty, source, script, and placeholder init inputs

- rejects absent, empty, source, script, and placeholder init inputs
   - Expected: initramfs_init_artifact_admission("", [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8]).is_ok() is false
   - Expected: initramfs_init_artifact_admission("build/os/simpleos-init", []).is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects absent, empty, source, script, and placeholder init inputs")
expect(initramfs_init_artifact_admission("", [0x7Fu8, 0x45u8, 0x4Cu8, 0x46u8]).is_ok()).to_equal(false)
expect(initramfs_init_artifact_admission("build/os/simpleos-init", []).is_ok()).to_equal(false)
expect(initramfs_init_artifact_admission(
    "src/app/simpleos/init.spl", _smf_fixture(1u8)).is_ok()).to_equal(false)
expect(initramfs_init_artifact_admission(
    "build/os/init.shs", _script_fixture()).is_ok()).to_equal(false)
expect(initramfs_init_artifact_admission(
    "build/os/placeholder", _script_fixture()).is_ok()).to_equal(false)
```

</details>

#### admits only native executables at the exact path for each tool role

- admits only native executables at the exact path for each tool role


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits only native executables at the exact path for each tool role")
expect(initramfs_tool_role_artifact_admission(
    "compiler", COMPILER_PATHS[0], _elf_fixture(2u8)).is_ok()).to_equal(true)
expect(initramfs_tool_role_artifact_admission(
    "interpreter", INTERPRETER_PATHS[0], _smf_fixture(3u8)).is_ok()).to_equal(true)
expect(initramfs_tool_role_artifact_admission(
    "loader", LOADER_PATHS[0], [8u8, 9u8, 10u8]).is_ok()).to_equal(false)
expect(initramfs_tool_role_artifact_admission(
    "loader", INTERPRETER_PATHS[0], _elf_fixture(4u8)).is_ok()).to_equal(false)
```

</details>

#### rejects SMF init envelopes with ambiguous role, arch, ABI, or stub metadata

- rejects SMF init envelopes with ambiguous role, arch, ABI, or stub metadata
   - Expected: initramfs_init_artifact_admission("build/os/init.smf", wrong_role).is_ok() is false
   - Expected: initramfs_init_artifact_admission("build/os/init.smf", wrong_arch).is_ok() is false
   - Expected: initramfs_init_artifact_admission("build/os/init.smf", wrong_abi).is_ok() is false
   - Expected: initramfs_init_artifact_admission("build/os/init.smf", missing_stub).is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects SMF init envelopes with ambiguous role, arch, ABI, or stub metadata")
var wrong_role = _smf_fixture(1u8)
wrong_role[124] = 2u8
expect(initramfs_init_artifact_admission("build/os/init.smf", wrong_role).is_ok()).to_equal(false)
var wrong_arch = _smf_fixture(1u8)
wrong_arch[125] = 3u8
expect(initramfs_init_artifact_admission("build/os/init.smf", wrong_arch).is_ok()).to_equal(false)
var wrong_abi = _smf_fixture(1u8)
wrong_abi[126] = 0u8
expect(initramfs_init_artifact_admission("build/os/init.smf", wrong_abi).is_ok()).to_equal(false)
var missing_stub = _smf_fixture(1u8)
missing_stub[116] = 0u8
expect(initramfs_init_artifact_admission("build/os/init.smf", missing_stub).is_ok()).to_equal(false)
```

</details>

#### admits only non-overlapping task-owned build paths before mutation

- admits only non-overlapping task-owned build paths before mutation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits only non-overlapping task-owned build paths before mutation")
expect(initramfs_pack_path_admission(
    "build/os/initramfs-staging", "build/os/initramfs.img.zst").is_ok()).to_equal(true)
expect(initramfs_pack_path_admission(
    "build/os/custom-image.staging", "build/os/custom-image.zst").is_ok()).to_equal(true)
```

</details>

#### preflights newc payload sizes before reading archive inputs

- preflights newc payload sizes before reading archive inputs
   - Expected: initramfs_pack_newc_entry_size("sbin/init", 64).is_ok() is true
   - Expected: initramfs_pack_newc_entry_size("sbin/init", -1).is_ok() is false
   - Expected: initramfs_pack_newc_entry_size("sbin/init", 536870912).is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preflights newc payload sizes before reading archive inputs")
expect(initramfs_pack_newc_entry_size("sbin/init", 64).is_ok()).to_equal(true)
expect(initramfs_pack_newc_entry_size("sbin/init", -1).is_ok()).to_equal(false)
expect(initramfs_pack_newc_entry_size("sbin/init", 536870912).is_ok()).to_equal(false)
```

</details>

#### rejects broad, absolute, dot, traversal, and overlapping staging paths

- rejects broad, absolute, dot, traversal, and overlapping staging paths
   - Expected: initramfs_pack_path_admission(staging, "build/os/image.zst").is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects broad, absolute, dot, traversal, and overlapping staging paths")
val unsafe_staging = [
    "/", ".", "..", "build", "build/os", "build/os/../escape.staging",
    "build/os/./image.staging", "build/os/image.staging/../escape",
    "tmp/image.staging", "build/os/nested/image.staging", "build/os/image",
    "build/os/image.staging/",
]
for staging in unsafe_staging:
    expect(initramfs_pack_path_admission(staging, "build/os/image.zst").is_ok()).to_equal(false)
expect(initramfs_pack_path_admission(
    "build/os/image.staging", "build/os/image.staging/output.zst").is_ok()).to_equal(false)
expect(initramfs_pack_path_admission(
    "build/os/image.staging", "build/os/nested/output.zst").is_ok()).to_equal(false)
```

</details>

#### rejects controls and shell metacharacters without executing them

- rejects controls and shell metacharacters without executing them
   - Expected: initramfs_pack_path_admission(staging, "build/os/image.zst").is_ok() is false
   - Expected: initramfs_pack_path_admission("build/os/image.staging", output).is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects controls and shell metacharacters without executing them")
val injected = [
    "build/os/image;touch-owned.staging", "build/os/image$(id).staging",
    "build/os/image`id`.staging", "build/os/image|tee.staging",
    "build/os/image&job.staging", "build/os/image\nnext.staging",
    "build/os/image\targ.staging", "build/os/image space.staging",
]
for staging in injected:
    expect(initramfs_pack_path_admission(staging, "build/os/image.zst").is_ok()).to_equal(false)
for output in injected:
    expect(initramfs_pack_path_admission("build/os/image.staging", output).is_ok()).to_equal(false)
```

</details>

#### renders only security-relevant role, path, and digest bindings

- renders only security-relevant role, path, and digest bindings
   - Expected: rendered does not contain `artifact:`
   - Expected: rendered.split("\n").len() equals `COMPILER_PATHS.len() + INTERPRETER_PATHS.len() + LOADER_PATHS.len() + 5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders only security-relevant role, path, and digest bindings")
val rendered = _render_fixture_manifest(
    sha256_u8_hex([1u8]), sha256_u8_hex([2u8]), sha256_u8_hex([3u8]))
expect(rendered.contains("artifact:")).to_equal(false)
expect(rendered.split("\n").len()).to_equal(COMPILER_PATHS.len() + INTERPRETER_PATHS.len() + LOADER_PATHS.len() + 5)
```

</details>

#### accepts one canonical archive whose manifest hashes every distinct role payload

- accepts one canonical archive whose manifest hashes every distinct role payload
   - Expected: validate_cpio_toolchain_archive(archive).is_ok() is true
   - Expected: validate_zstd_toolchain_archive(compress_zstd(archive)).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts one canonical archive whose manifest hashes every distinct role payload")
val archive = _archive("", false, false)
expect(validate_cpio_toolchain_archive(archive).is_ok()).to_equal(true)
expect(validate_zstd_toolchain_archive(compress_zstd(archive)).is_ok()).to_equal(true)
```

</details>

#### fails closed on truncated and non-hex newc headers

- fails closed on truncated and non-hex newc headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on truncated and non-hex newc headers")
expect(cpio_parse_bounded(
    [0x30u8, 0x37u8, 0x30u8], 16, 256, 4096).unwrap_err()).to_equal("cpio-header-truncated")
var invalid_hex = _archive("", false, false)
invalid_hex[6] = 0x67u8
expect(cpio_parse_bounded(
    invalid_hex, 131072, 4096, 536870912).unwrap_err()).to_equal("cpio-header-hex-invalid")
var prefix_attack = NewcArchiveWriter(data: [], inode: 1)
prefix_attack.entry("ok", 0x81A4, [1u8])
prefix_attack.entry("TRAILER!!!", 0, [])
prefix_attack.data[120] = 0u8
expect(cpio_parse_bounded(
    prefix_attack.data, 16, 256, 4096).unwrap_err()).to_equal("cpio-magic-invalid")
```

</details>

#### fails closed before indexing oversized newc names and payloads

- fails closed before indexing oversized newc names and payloads


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed before indexing oversized newc names and payloads")
var oversized_name = _archive("", false, false)
var i: i64 = 94
while i < 102:
    oversized_name[i] = 0x66u8
    i = i + 1
expect(cpio_parse_bounded(
    oversized_name, 131072, 4096, 536870912).unwrap_err()).to_equal("cpio-name-size-invalid")
var oversized_payload = _archive("", false, false)
i = 54
while i < 62:
    oversized_payload[i] = 0x66u8
    i = i + 1
expect(cpio_parse_bounded(
    oversized_payload, 131072, 4096, 536870912).unwrap_err()).to_equal("cpio-payload-truncated")
```

</details>

#### rejects trailing data after the one bounded zstd frame

- rejects trailing data after the one bounded zstd frame
   - Expected: validate_zstd_toolchain_archive(compressed).unwrap_err() equals `zstd-chained-or-trailing-frame-rejected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trailing data after the one bounded zstd frame")
var compressed = _zstd_raw_frame(_archive("", false, false))
compressed.push(1u8)
expect(validate_zstd_toolchain_archive(compressed).unwrap_err()).to_equal("zstd-chained-or-trailing-frame-rejected")
```

</details>

#### rejects duplicate canonical paths

- rejects duplicate canonical paths
   - Expected: validate_cpio_toolchain_archive(_archive("duplicate", false, false)).unwrap_err() equals `archive-path-duplicate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects duplicate canonical paths")
expect(validate_cpio_toolchain_archive(_archive("duplicate", false, false)).unwrap_err()).to_equal("archive-path-duplicate")
```

</details>

#### rejects traversal and symlink entries before extraction

- rejects traversal and symlink entries before extraction
   - Expected: validate_cpio_toolchain_archive(_archive("traversal", false, false)).unwrap_err() equals `archive-path-traversal`
   - Expected: validate_cpio_toolchain_archive(_archive("symlink", false, false)).unwrap_err() equals `archive-entry-type-unsafe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects traversal and symlink entries before extraction")
expect(validate_cpio_toolchain_archive(_archive("traversal", false, false)).unwrap_err()).to_equal("archive-path-traversal")
expect(validate_cpio_toolchain_archive(_archive("symlink", false, false)).unwrap_err()).to_equal("archive-entry-type-unsafe")
expect(cpio_parse_bounded(
    _archive("traversal", false, false), 131072, 4096, 536870912).unwrap_err()).to_equal("cpio-path-not-canonical")
expect(cpio_parse_bounded(
    _archive("symlink", false, false), 131072, 4096, 536870912).unwrap_err()).to_equal("cpio-entry-type-unsafe")
```

</details>

#### rejects manifest digests that do not match archived bytes

- rejects manifest digests that do not match archived bytes
   - Expected: validate_cpio_toolchain_archive(_archive("", true, false)).unwrap_err() equals `toolchain-role-payload-digest-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects manifest digests that do not match archived bytes")
expect(validate_cpio_toolchain_archive(_archive("", true, false)).unwrap_err()).to_equal("toolchain-role-payload-digest-mismatch")
```

</details>

#### rejects a source or placeholder payload archived at /sbin/init

- rejects a source or placeholder payload archived at /sbin/init


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a source or placeholder payload archived at /sbin/init")
expect(validate_cpio_toolchain_archive(
    _archive("placeholder-init", false, false)).unwrap_err()).to_equal("init-artifact-native-format-invalid")
```

</details>

#### rejects reusing a toolchain role as the init artifact

- rejects reusing a toolchain role as the init artifact


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects reusing a toolchain role as the init artifact")
expect(validate_cpio_toolchain_archive(
    _archive("init-role-reuse", false, false)).unwrap_err()).to_equal("toolchain-role-digests-not-distinct")
```

</details>

#### rejects wrong role binding and duplicate binding declarations

- rejects wrong role binding and duplicate binding declarations
   - Expected: validate_cpio_toolchain_archive(_archive("wrong-role", false, false)).unwrap_err() equals `toolchain-manifest-role-binding-invalid`
   - Expected: validate_cpio_toolchain_archive(_archive("duplicate-binding", false, false)).unwrap_err() equals `toolchain-manifest-path-duplicate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects wrong role binding and duplicate binding declarations")
expect(validate_cpio_toolchain_archive(_archive("wrong-role", false, false)).unwrap_err()).to_equal("toolchain-manifest-role-binding-invalid")
expect(validate_cpio_toolchain_archive(_archive("duplicate-binding", false, false)).unwrap_err()).to_equal("toolchain-manifest-path-duplicate")
```

</details>

#### rejects removed host artifact metadata instead of ignoring it

- rejects removed host artifact metadata instead of ignoring it
   - Expected: validate_cpio_toolchain_archive(_archive("artifact-scalar", false, false)).is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects removed host artifact metadata instead of ignoring it")
expect(validate_cpio_toolchain_archive(_archive("artifact-scalar", false, false)).is_ok()).to_equal(false)
```

</details>

#### rejects role reuse even when each manifest digest matches

- rejects role reuse even when each manifest digest matches
   - Expected: validate_cpio_toolchain_archive(_archive("", false, true)).unwrap_err() equals `toolchain-role-digests-not-distinct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects role reuse even when each manifest digest matches")
expect(validate_cpio_toolchain_archive(_archive("", false, true)).unwrap_err()).to_equal("toolchain-role-digests-not-distinct")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/port/initramfs_pack_archive_validation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS initramfs archive role validation.
- SimpleOS initramfs archive role validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `ec7734ccb6d7e1094a33afb292f1b5814b4f39f95b942f6612224095fbd93fe5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec7734ccb6d7e1094a33afb292f1b5814b4f39f95b942f6612224095fbd93fe5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec7734ccb6d7e1094a33afb292f1b5814b4f39f95b942f6612224095fbd93fe5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/port/initramfs_pack_archive_validation_spec.spl
mirror: doc/06_spec/01_unit/os/port/initramfs_pack_archive_validation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/port/initramfs_pack_archive_validation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/port/initramfs_pack_archive_validation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/port/initramfs_pack_archive_validation_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits explicit target-native ELF and SMF init artifacts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/initramfs_pack_archive_validation_spec.spl:179:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects absent, empty, source, script, and placeholder init inputs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/port/initramfs_pack_archive_validation_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits only native executables at the exact path for each tool role' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

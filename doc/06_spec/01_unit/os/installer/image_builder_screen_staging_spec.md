# Image Builder Screen Staging Specification

> Tests covering Image builder screen selection staging.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Image Builder Screen Staging Specification

## Scenarios

### Image builder screen selection staging

#### keeps a default image's rc.conf byte-identical to the pre-A5 template

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps a default image's rc.conf byte-identical to the pre-A5 template
- Build an image with no screen request
   - Expected: result.is_ok() is true
- The staged /etc/rc.conf equals today's literal exactly
   - Expected: rc_conf equals `_PRE_A5_RC_CONF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps a default image's rc.conf byte-identical to the pre-A5 template")
step("Build an image with no screen request")
val dir = "build/test-artifacts/image-builder-screen-default"
_reset_dir(dir)
val output = "{dir}/simpleos-arm64-default.img"
val result = build_install_image(PkgArch.Arm64, "", "", output, 64)
expect(result.is_ok()).to_equal(true)
step("The staged /etc/rc.conf equals today's literal exactly")
val rc_conf = rt_file_read_text("{output}.contents/rootfs/etc/rc.conf")
expect(rc_conf).to_equal(_PRE_A5_RC_CONF)
```

</details>

#### stages screen_type, screen_res and screen_simd when the build requests them

- stages screen_type, screen_res and screen_simd when the build requests them
- Request a 2d screen at 1024x768 with avx2 before building
   - Expected: image_builder_set_screen("2d", "1024x768", "avx2").is_ok() is true
   - Expected: result.is_ok() is true
- All three keys land in the staged /etc/rc.conf, base template intact
   - Expected: rc_conf equals `_PRE_A5_RC_CONF + "screen_type="2d"\nscreen_res="1024x768"\nscreen_simd="avx2... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("stages screen_type, screen_res and screen_simd when the build requests them")
step("Request a 2d screen at 1024x768 with avx2 before building")
val dir = "build/test-artifacts/image-builder-screen-2d"
_reset_dir(dir)
val output = "{dir}/simpleos-arm64-2d.img"
expect(image_builder_set_screen("2d", "1024x768", "avx2").is_ok()).to_equal(true)
val result = build_install_image(PkgArch.Arm64, "", "", output, 64)
expect(result.is_ok()).to_equal(true)
step("All three keys land in the staged /etc/rc.conf, base template intact")
val rc_conf = rt_file_read_text("{output}.contents/rootfs/etc/rc.conf")
expect(rc_conf).to_equal(_PRE_A5_RC_CONF + "screen_type=\"2d\"\nscreen_res=\"1024x768\"\nscreen_simd=\"avx2\"\n")
```

</details>

#### consumes the request so a later build reverts to the default

- consumes the request so a later build reverts to the default
- Build again after the 2d example above, with no new request
   - Expected: build_install_image(PkgArch.Arm64, "", "", output, 64).is_ok() is true
- No screen keys leaked from the previous build
   - Expected: rt_file_read_text("{output}.contents/rootfs/etc/rc.conf") equals `_PRE_A5_RC_CONF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("consumes the request so a later build reverts to the default")
step("Build again after the 2d example above, with no new request")
val dir = "build/test-artifacts/image-builder-screen-consume"
_reset_dir(dir)
val output = "{dir}/simpleos-arm64-after-2d.img"
expect(build_install_image(PkgArch.Arm64, "", "", output, 64).is_ok()).to_equal(true)
step("No screen keys leaked from the previous build")
expect(rt_file_read_text("{output}.contents/rootfs/etc/rc.conf")).to_equal(_PRE_A5_RC_CONF)
```

</details>

#### rejects unrecognized screen values instead of silently staging wm

- rejects unrecognized screen values instead of silently staging wm
- An invalid screen_type is an error, not a normalization
- Malformed screen_res and unknown screen_simd fail too


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects unrecognized screen values instead of silently staging wm")
step("An invalid screen_type is an error, not a normalization")
val bad_type = image_builder_set_screen("quake", "", "")
expect(bad_type.is_err()).to_be(true)
if val Err(message) = bad_type:
    expect(message).to_contain("screen_type invalid")
step("Malformed screen_res and unknown screen_simd fail too")
expect(image_builder_set_screen("2d", "1024by768", "").is_err()).to_be(true)
expect(image_builder_set_screen("2d", "", "mmx").is_err()).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/installer/image_builder_screen_staging_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Image builder screen selection staging.
- Image builder screen selection staging

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `59da2ff8468b1cfdb6592f5a32e269c319fca924b54291ea2b2a9741e837f0bd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59da2ff8468b1cfdb6592f5a32e269c319fca924b54291ea2b2a9741e837f0bd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59da2ff8468b1cfdb6592f5a32e269c319fca924b54291ea2b2a9741e837f0bd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/installer/image_builder_screen_staging_spec.spl
mirror: doc/06_spec/01_unit/os/installer/image_builder_screen_staging_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/installer/image_builder_screen_staging_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/installer/image_builder_screen_staging_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/installer/image_builder_screen_staging_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps a default image's rc.conf byte-identical to the pre-A5 template' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/image_builder_screen_staging_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stages screen_type, screen_res and screen_simd when the build requests them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/installer/image_builder_screen_staging_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'consumes the request so a later build reverts to the default' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

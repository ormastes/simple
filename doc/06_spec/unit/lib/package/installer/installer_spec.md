# Installer Specification

> Tests covering InstallerPlatform, InstallerConfig, ToolAvailability, InstallerResult.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Installer Specification

## Scenarios

### InstallerPlatform

#### enum values

#### has all 5 platforms

- has all 5 platforms
   - Expected: platforms.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has all 5 platforms")
val platforms = InstallerPlatform.all()
expect(platforms.len()).to_equal(5)
```

</details>

#### converts to string

- converts to string
   - Expected: InstallerPlatform.Deb.to_string() equals `deb`
   - Expected: InstallerPlatform.Rpm.to_string() equals `rpm`
   - Expected: InstallerPlatform.MacosPkg.to_string() equals `macos`
   - Expected: InstallerPlatform.FreeBsd.to_string() equals `freebsd`
   - Expected: InstallerPlatform.WindowsExe.to_string() equals `windows`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to string")
expect(InstallerPlatform.Deb.to_string()).to_equal("deb")
expect(InstallerPlatform.Rpm.to_string()).to_equal("rpm")
expect(InstallerPlatform.MacosPkg.to_string()).to_equal("macos")
expect(InstallerPlatform.FreeBsd.to_string()).to_equal("freebsd")
expect(InstallerPlatform.WindowsExe.to_string()).to_equal("windows")
```

</details>

#### parses from string

- parses from string
   - Expected: deb == nil is false
   - Expected: unknown == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses from string")
val deb = InstallerPlatform.from_string("deb")
expect(deb == nil).to_equal(false)

val unknown = InstallerPlatform.from_string("invalid")
expect(unknown == nil).to_equal(true)
```

</details>

#### file extensions

#### returns correct extensions

- returns correct extensions
   - Expected: InstallerPlatform.Deb.file_extension() equals `.deb`
   - Expected: InstallerPlatform.Rpm.file_extension() equals `.rpm`
   - Expected: InstallerPlatform.MacosPkg.file_extension() equals `.pkg`
   - Expected: InstallerPlatform.FreeBsd.file_extension() equals `.txz`
   - Expected: InstallerPlatform.WindowsExe.file_extension() equals `.exe`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct extensions")
expect(InstallerPlatform.Deb.file_extension()).to_equal(".deb")
expect(InstallerPlatform.Rpm.file_extension()).to_equal(".rpm")
expect(InstallerPlatform.MacosPkg.file_extension()).to_equal(".pkg")
expect(InstallerPlatform.FreeBsd.file_extension()).to_equal(".txz")
expect(InstallerPlatform.WindowsExe.file_extension()).to_equal(".exe")
```

</details>

#### FPM type mapping

#### returns FPM types for supported platforms

- returns FPM types for supported platforms
   - Expected: InstallerPlatform.Deb.fpm_type() == nil is false
   - Expected: InstallerPlatform.Rpm.fpm_type() == nil is false
   - Expected: InstallerPlatform.MacosPkg.fpm_type() == nil is false
   - Expected: InstallerPlatform.FreeBsd.fpm_type() == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns FPM types for supported platforms")
expect(InstallerPlatform.Deb.fpm_type() == nil).to_equal(false)
expect(InstallerPlatform.Rpm.fpm_type() == nil).to_equal(false)
expect(InstallerPlatform.MacosPkg.fpm_type() == nil).to_equal(false)
expect(InstallerPlatform.FreeBsd.fpm_type() == nil).to_equal(false)
```

</details>

#### returns nil for Windows (uses NSIS)

- returns nil for Windows (uses NSIS)
   - Expected: InstallerPlatform.WindowsExe.fpm_type() == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for Windows (uses NSIS)")
expect(InstallerPlatform.WindowsExe.fpm_type() == nil).to_equal(true)
```

</details>

#### descriptions

#### provides human-readable descriptions

- provides human-readable descriptions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides human-readable descriptions")
expect(InstallerPlatform.Deb.description()).to_contain("Debian")
expect(InstallerPlatform.WindowsExe.description()).to_contain("Windows")
```

</details>

### InstallerConfig

#### default config

#### creates config with sensible defaults

- creates config with sensible defaults
   - Expected: config.package_name equals `simple-lang`
   - Expected: config.output_dir equals `build/installers`
   - Expected: config.architecture equals `amd64`
   - Expected: config.license equals `MIT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates config with sensible defaults")
val config = default_config()
expect(config.package_name).to_equal("simple-lang")
expect(config.output_dir).to_equal("build/installers")
expect(config.architecture).to_equal("amd64")
expect(config.license).to_equal("MIT")
```

</details>

#### has valid homepage URL

- has valid homepage URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has valid homepage URL")
val config = default_config()
expect(config.homepage).to_start_with("https://")
```

</details>

### ToolAvailability

#### tool detection

#### detects tools without crashing

- detects tools without crashing
   - Expected: tools.fpm_available == true or tools.fpm_available == false is true
   - Expected: tools.makensis_available == true or tools.makensis_available == false is true
   - Expected: tools.dpkg_deb_available == true or tools.dpkg_deb_available == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects tools without crashing")
val tools = detect_all_tools()
# Just verify the struct is populated (tools may or may not be installed)
expect(tools.fpm_available == true or tools.fpm_available == false).to_equal(true)
expect(tools.makensis_available == true or tools.makensis_available == false).to_equal(true)
expect(tools.dpkg_deb_available == true or tools.dpkg_deb_available == false).to_equal(true)
```

</details>

#### tool checking per platform

#### requires FPM or dpkg-deb for Debian

- requires FPM or dpkg-deb for Debian
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires FPM or dpkg-deb for Debian")
val tools = ToolAvailability(
    fpm_available: false, makensis_available: false, dpkg_deb_available: true,
    fpm_path: "", makensis_path: "", dpkg_deb_path: "/usr/bin/dpkg-deb"
)
val result = check_tool_for_platform(InstallerPlatform.Deb, tools)
expect(result.is_ok()).to_equal(true)
```

</details>

#### requires FPM for RPM

- requires FPM for RPM
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires FPM for RPM")
val tools = ToolAvailability(
    fpm_available: false, makensis_available: false, dpkg_deb_available: false,
    fpm_path: "", makensis_path: "", dpkg_deb_path: ""
)
val result = check_tool_for_platform(InstallerPlatform.Rpm, tools)
expect(result.is_err()).to_equal(true)
```

</details>

#### requires makensis for Windows

- requires makensis for Windows
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires makensis for Windows")
val tools = ToolAvailability(
    fpm_available: true, makensis_available: false, dpkg_deb_available: false,
    fpm_path: "/usr/bin/fpm", makensis_path: "", dpkg_deb_path: ""
)
val result = check_tool_for_platform(InstallerPlatform.WindowsExe, tools)
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts makensis for Windows

- accepts makensis for Windows
   - Expected: result.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts makensis for Windows")
val tools = ToolAvailability(
    fpm_available: false, makensis_available: true, dpkg_deb_available: false,
    fpm_path: "", makensis_path: "/usr/bin/makensis", dpkg_deb_path: ""
)
val result = check_tool_for_platform(InstallerPlatform.WindowsExe, tools)
expect(result.is_ok()).to_equal(true)
```

</details>

### InstallerResult

#### result construction

#### creates success result

- creates success result
   - Expected: result.success is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates success result")
val result = InstallerResult(
    platform: InstallerPlatform.Deb,
    success: true,
    output_path: "build/installers/simple-lang_0.9.3_amd64.deb",
    message: "Built successfully"
)
expect(result.success).to_equal(true)
expect(result.output_path).to_contain(".deb")
```

</details>

#### creates failure result

- creates failure result
   - Expected: result.success is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates failure result")
val result = InstallerResult(
    platform: InstallerPlatform.WindowsExe,
    success: false,
    output_path: "",
    message: "makensis not found"
)
expect(result.success).to_equal(false)
expect(result.message).to_contain("makensis")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/package/installer/installer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering InstallerPlatform, InstallerConfig, ToolAvailability, InstallerResult.
- InstallerPlatform
- InstallerConfig
- ToolAvailability
- InstallerResult

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `1b587b123f3be2f470d28b3c7f44517849d64ee8541b8ef2d1771ba4cf9ffb6e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1b587b123f3be2f470d28b3c7f44517849d64ee8541b8ef2d1771ba4cf9ffb6e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1b587b123f3be2f470d28b3c7f44517849d64ee8541b8ef2d1771ba4cf9ffb6e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/package/installer/installer_spec.spl
mirror: doc/06_spec/unit/lib/package/installer/installer_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/package/installer/installer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/package/installer/installer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/package/installer/installer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/package/installer/installer_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has all 5 platforms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/package/installer/installer_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/package/installer/installer_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses from string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

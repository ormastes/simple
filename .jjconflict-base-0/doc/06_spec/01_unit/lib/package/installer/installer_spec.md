# Installer Specification

> <details>

<!-- sdn-diagram:id=installer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=installer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

installer_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=installer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val platforms = InstallerPlatform.all()
expect(platforms.len()).to_equal(5)
```

</details>

#### converts to string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(InstallerPlatform.Deb.to_string()).to_equal("deb")
expect(InstallerPlatform.Rpm.to_string()).to_equal("rpm")
expect(InstallerPlatform.MacosPkg.to_string()).to_equal("macos")
expect(InstallerPlatform.FreeBsd.to_string()).to_equal("freebsd")
expect(InstallerPlatform.WindowsExe.to_string()).to_equal("windows")
```

</details>

#### parses from string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deb = InstallerPlatform.from_string("deb")
expect(deb.?).to_equal(true)

val unknown = InstallerPlatform.from_string("invalid")
expect(unknown.?).to_equal(false)
```

</details>

#### file extensions

#### returns correct extensions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(InstallerPlatform.Deb.file_extension()).to_equal(".deb")
expect(InstallerPlatform.Rpm.file_extension()).to_equal(".rpm")
expect(InstallerPlatform.MacosPkg.file_extension()).to_equal(".pkg")
expect(InstallerPlatform.FreeBsd.file_extension()).to_equal(".txz")
expect(InstallerPlatform.WindowsExe.file_extension()).to_equal(".exe")
```

</details>

#### FPM type mapping

#### returns FPM types for supported platforms

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(InstallerPlatform.Deb.fpm_type().?).to_equal(true)
expect(InstallerPlatform.Rpm.fpm_type().?).to_equal(true)
expect(InstallerPlatform.MacosPkg.fpm_type().?).to_equal(true)
expect(InstallerPlatform.FreeBsd.fpm_type().?).to_equal(true)
```

</details>

#### returns nil for Windows (uses NSIS)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(InstallerPlatform.WindowsExe.fpm_type().?).to_equal(false)
```

</details>

#### descriptions

#### provides human-readable descriptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(InstallerPlatform.Deb.description()).to_contain("Debian")
expect(InstallerPlatform.WindowsExe.description()).to_contain("Windows")
```

</details>

### InstallerConfig

#### default config

#### creates config with sensible defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_config()
expect(config.package_name).to_equal("simple-lang")
expect(config.output_dir).to_equal("build/installers")
expect(config.architecture).to_equal("amd64")
expect(config.license).to_equal("MIT")
```

</details>

#### has valid homepage URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_config()
expect(config.homepage).to_start_with("https://")
```

</details>

### ToolAvailability

#### tool detection

#### detects tools without crashing

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = detect_all_tools()
# Just verify the struct is populated (tools may or may not be installed)
expect(tools.fpm_available == true or tools.fpm_available == false).to_equal(true)
expect(tools.makensis_available == true or tools.makensis_available == false).to_equal(true)
expect(tools.dpkg_deb_available == true or tools.dpkg_deb_available == false).to_equal(true)
```

</details>

#### tool checking per platform

#### requires FPM or dpkg-deb for Debian

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = ToolAvailability(
    fpm_available: false, makensis_available: false, dpkg_deb_available: true,
    fpm_path: "", makensis_path: "", dpkg_deb_path: "/usr/bin/dpkg-deb"
)
val result = check_tool_for_platform(InstallerPlatform.Deb, tools)
expect(result.is_ok()).to_equal(true)
```

</details>

#### requires FPM for RPM

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = ToolAvailability(
    fpm_available: false, makensis_available: false, dpkg_deb_available: false,
    fpm_path: "", makensis_path: "", dpkg_deb_path: ""
)
val result = check_tool_for_platform(InstallerPlatform.Rpm, tools)
expect(result.is_err()).to_equal(true)
```

</details>

#### requires makensis for Windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = ToolAvailability(
    fpm_available: true, makensis_available: false, dpkg_deb_available: false,
    fpm_path: "/usr/bin/fpm", makensis_path: "", dpkg_deb_path: ""
)
val result = check_tool_for_platform(InstallerPlatform.WindowsExe, tools)
expect(result.is_err()).to_equal(true)
```

</details>

#### accepts makensis for Windows

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/package/installer/installer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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

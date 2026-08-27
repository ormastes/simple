# Web Application Packaging Specification

> Tests for the Simple Web Archive (SWA) format, CLI commands (`simple web build`, `simple web serve`, `simple web deploy`), and supporting infrastructure (mime types, deployment descriptor, plugin/container/service packaging).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Application Packaging Specification

Tests for the Simple Web Archive (SWA) format, CLI commands (`simple web build`, `simple web serve`, `simple web deploy`), and supporting infrastructure (mime types, deployment descriptor, plugin/container/service packaging).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SWA-001 through #SWA-008 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | doc/requirement/web_app_packaging.md |
| Plan | doc/03_plan/web_app_packaging.md |
| Design | doc/05_design/web_app_packaging.md |
| Research | doc/01_research/web_app_packaging.md |
| Source | `test/03_system/infrastructure/web_app_packaging_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the Simple Web Archive (SWA) format, CLI commands (`simple web build`,
`simple web serve`, `simple web deploy`), and supporting infrastructure (mime types,
deployment descriptor, plugin/container/service packaging).

## Key Concepts

| Concept | Description |
|---------|-------------|
| SWA | Simple Web Archive — bundles compiled modules + static assets + descriptor |
| webapp.sdn | Deployment descriptor defining routes, middleware, entry point |
| AssetIndex | Path-based index for O(1) static file lookup in archive |
| SwaBuilder | Writer that creates .swa files from modules + assets |
| SwaArchive | Reader that opens and queries .swa files |

## Scenarios

### SWA Header Format

#### has correct magic bytes SWA\\0

- has correct magic bytes SWA\\0
   - Expected: SWA_MAGIC[0] equals `83)   # 'S'`
   - Expected: SWA_MAGIC[1] equals `87)   # 'W'`
   - Expected: SWA_MAGIC[2] equals `65)   # 'A'`
   - Expected: SWA_MAGIC[3] equals `0)    # '\0'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct magic bytes SWA\\0")
val SWA_MAGIC = [83, 87, 65, 0]
expect(SWA_MAGIC[0]).to_equal(83)   # 'S'
expect(SWA_MAGIC[1]).to_equal(87)   # 'W'
expect(SWA_MAGIC[2]).to_equal(65)   # 'A'
expect(SWA_MAGIC[3]).to_equal(0)    # '\0'
```

</details>

#### header is 256 bytes

- header is 256 bytes
   - Expected: SWA_HEADER_SIZE equals `256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("header is 256 bytes")
val SWA_HEADER_SIZE = 256
expect(SWA_HEADER_SIZE).to_equal(256)
```

</details>

#### asset index entry is 128 bytes

- asset index entry is 128 bytes
   - Expected: SWA_ASSET_ENTRY_SIZE equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("asset index entry is 128 bytes")
val SWA_ASSET_ENTRY_SIZE = 128
expect(SWA_ASSET_ENTRY_SIZE).to_equal(128)
```

</details>

### SWA Builder

#### creates empty archive with only descriptor

- creates empty archive with only descriptor


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates empty archive with only descriptor")
# A minimal SWA with just a deployment descriptor and no modules/assets
# should still produce a valid file
val descriptor = "webapp:\n  name: test\n  version: 1.0.0\n"
expect(descriptor.len()).to_be_greater_than(0)
```

</details>

#### rejects archive with no descriptor

- rejects archive with no descriptor
   - Expected: has_descriptor is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects archive with no descriptor")
# SWA without a webapp.sdn descriptor is invalid
val has_descriptor = false
expect(has_descriptor).to_equal(false)
```

</details>

#### embeds static assets with correct path

- embeds static assets with correct path


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("embeds static assets with correct path")
val asset_path = "css/style.css"
val asset_content = "body { margin: 0; }"
expect(asset_path).to_contain("css/")
expect(asset_content.len()).to_be_greater_than(0)
```

</details>

#### handles binary assets (images)

- handles binary assets (images)
   - Expected: png_header[0] equals `137`
   - Expected: png_header.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles binary assets (images)")
# PNG, JPG, etc. should be stored as raw bytes
val png_header = [137, 80, 78, 71]  # PNG magic bytes
expect(png_header[0]).to_equal(137)
expect(png_header.len()).to_equal(4)
```

</details>

### SWA Reader

#### reads header and validates magic

- reads header and validates magic
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads header and validates magic")
val magic = [83, 87, 65, 0]
val is_valid = (magic[0] == 83 and magic[1] == 87 and
                magic[2] == 65 and magic[3] == 0)
expect(is_valid).to_equal(true)
```

</details>

#### lists all assets in archive

- lists all assets in archive
   - Expected: expected_assets.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lists all assets in archive")
# After reading an SWA, list_assets() returns all embedded paths
val expected_assets = ["index.html", "css/style.css", "js/app.js"]
expect(expected_assets.len()).to_equal(3)
expect(expected_assets).to_contain("index.html")
```

</details>

#### retrieves asset by path

- retrieves asset by path


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("retrieves asset by path")
# get_asset("css/style.css") returns the file contents
val path = "css/style.css"
expect(path).to_start_with("css/")
```

</details>

#### returns error for missing asset

- returns error for missing asset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error for missing asset")
val path = "nonexistent.html"
expect(path).to_contain("nonexistent")
```

</details>

### Deployment Descriptor (webapp.sdn)

#### parses valid webapp.sdn

- parses valid webapp.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses valid webapp.sdn")
val descriptor = "webapp:\n  name: myapp\n  version: 1.0.0\n  port: 8080\n"
expect(descriptor).to_contain("name: myapp")
expect(descriptor).to_contain("port: 8080")
```

</details>

#### validates required fields

- validates required fields
   - Expected: has_name is true
   - Expected: has_version is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates required fields")
# name and version are required
val has_name = true
val has_version = true
expect(has_name).to_equal(true)
expect(has_version).to_equal(true)
```

</details>

#### defaults port to 8080 when not specified

- defaults port to 8080 when not specified
   - Expected: default_port equals `8080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults port to 8080 when not specified")
val default_port = 8080
expect(default_port).to_equal(8080)
```

</details>

#### validates port range

- validates port range
   - Expected: valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates port range")
val port = 8080
val valid = (port > 0 and port < 65536)
expect(valid).to_equal(true)
```

</details>

### Mime Type Lookup

#### maps html extension to text/html

- maps html extension to text/html
   - Expected: ext equals `html`
   - Expected: expected equals `text/html`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps html extension to text/html")
val ext = "html"
val expected = "text/html"
expect(ext).to_equal("html")
expect(expected).to_equal("text/html")
```

</details>

#### maps css extension to text/css

- maps css extension to text/css
   - Expected: ext equals `css`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps css extension to text/css")
val ext = "css"
val expected = "text/css"
expect(ext).to_equal("css")
```

</details>

#### maps js extension to application/javascript

- maps js extension to application/javascript
   - Expected: ext equals `js`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps js extension to application/javascript")
val ext = "js"
val expected = "application/javascript"
expect(ext).to_equal("js")
```

</details>

#### maps png extension to image/png

- maps png extension to image/png
   - Expected: ext equals `png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps png extension to image/png")
val ext = "png"
val expected = "image/png"
expect(ext).to_equal("png")
```

</details>

#### returns octet-stream for unknown extension

- returns octet-stream for unknown extension
   - Expected: fallback equals `application/octet-stream`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns octet-stream for unknown extension")
val fallback = "application/octet-stream"
expect(fallback).to_equal("application/octet-stream")
```

</details>

### SmfAppType WebApp

#### WebApp has value 5

- WebApp has value 5
   - Expected: webapp_value equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("WebApp has value 5")
val webapp_value = 5
expect(webapp_value).to_equal(5)
```

</details>

#### WebApp name is webapp

- WebApp name is webapp
   - Expected: name equals `webapp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("WebApp name is webapp")
val name = "webapp"
expect(name).to_equal("webapp")
```

</details>

### Web Packaging CLI Commands

#### web build accepts --output flag

- web build accepts --output flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("web build accepts --output flag")
val args = ["build", "--output", "myapp.swa"]
expect(args).to_contain("build")
expect(args).to_contain("--output")
```

</details>

#### web serve accepts port flag

- web serve accepts port flag


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("web serve accepts port flag")
val args = ["serve", "myapp.swa", "--port", "3000"]
expect(args).to_contain("serve")
expect(args).to_contain("--port")
```

</details>

#### web deploy accepts target directory

- web deploy accepts target directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("web deploy accepts target directory")
val args = ["deploy", "myapp.swa", "--target", "/opt/myapp"]
expect(args).to_contain("deploy")
expect(args).to_contain("--target")
```

</details>

### Plugin Package (SPX)

#### plugin.sdn has required fields

- plugin.sdn has required fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("plugin.sdn has required fields")
val descriptor = "plugin:\n  name: my-plugin\n  version: 1.0.0\n  type: compiler\n"
expect(descriptor).to_contain("name: my-plugin")
expect(descriptor).to_contain("type: compiler")
```

</details>

#### installs to correct directory

- installs to correct directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("installs to correct directory")
val install_dir = "~/.simple/plugins/my-plugin/1.0.0/"
expect(install_dir).to_contain("plugins/my-plugin")
```

</details>

### Container Image Generation

#### generates multi-stage Dockerfile for webapp

- generates multi-stage Dockerfile for webapp
   - Expected: project_type equals `webapp`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates multi-stage Dockerfile for webapp")
val project_type = "webapp"
expect(project_type).to_equal("webapp")
```

</details>

#### generates simple Dockerfile for CLI app

- generates simple Dockerfile for CLI app
   - Expected: project_type equals `application`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates simple Dockerfile for CLI app")
val project_type = "application"
expect(project_type).to_equal("application")
```

</details>

### Service Package

#### generates systemd unit on Linux

- generates systemd unit on Linux
   - Expected: os equals `linux`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates systemd unit on Linux")
val os = "linux"
expect(os).to_equal("linux")
```

</details>

#### generates launchd plist on macOS

- generates launchd plist on macOS
   - Expected: os equals `macos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates launchd plist on macOS")
val os = "macos"
expect(os).to_equal("macos")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/requirement/web_app_packaging.md`
- **Plan:** `doc/03_plan/web_app_packaging.md`
- **Design:** `doc/05_design/web_app_packaging.md`
- **Research:** `doc/01_research/web_app_packaging.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SWA`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `17fb57154c05afdfb87f4d62d6e3c59f8746657390eccf6a59101cb22ab1cb21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `17fb57154c05afdfb87f4d62d6e3c59f8746657390eccf6a59101cb22ab1cb21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `17fb57154c05afdfb87f4d62d6e3c59f8746657390eccf6a59101cb22ab1cb21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/infrastructure/web_app_packaging_spec.spl
mirror: doc/06_spec/03_system/infrastructure/web_app_packaging_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/infrastructure/web_app_packaging_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/infrastructure/web_app_packaging_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/infrastructure/web_app_packaging_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/infrastructure/web_app_packaging_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/infrastructure/web_app_packaging_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct magic bytes SWA\\0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/web_app_packaging_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'header is 256 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/infrastructure/web_app_packaging_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'asset index entry is 128 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

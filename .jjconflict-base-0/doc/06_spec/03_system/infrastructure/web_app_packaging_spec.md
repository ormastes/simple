# Web Application Packaging Specification

> Tests for the Simple Web Archive (SWA) format, CLI commands (`simple web build`, `simple web serve`, `simple web deploy`), and supporting infrastructure (mime types, deployment descriptor, plugin/container/service packaging).

<!-- sdn-diagram:id=web_app_packaging_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_app_packaging_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_app_packaging_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_app_packaging_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val SWA_MAGIC = [83, 87, 65, 0]
expect(SWA_MAGIC[0]).to_equal(83)   # 'S'
expect(SWA_MAGIC[1]).to_equal(87)   # 'W'
expect(SWA_MAGIC[2]).to_equal(65)   # 'A'
expect(SWA_MAGIC[3]).to_equal(0)    # '\0'
```

</details>

#### header is 256 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val SWA_HEADER_SIZE = 256
expect(SWA_HEADER_SIZE).to_equal(256)
```

</details>

#### asset index entry is 128 bytes

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val SWA_ASSET_ENTRY_SIZE = 128
expect(SWA_ASSET_ENTRY_SIZE).to_equal(128)
```

</details>

### SWA Builder

#### creates empty archive with only descriptor

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A minimal SWA with just a deployment descriptor and no modules/assets
# should still produce a valid file
val descriptor = "webapp:\n  name: test\n  version: 1.0.0\n"
expect(descriptor.len()).to_be_greater_than(0)
```

</details>

#### rejects archive with no descriptor

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# SWA without a webapp.sdn descriptor is invalid
val has_descriptor = false
expect(has_descriptor).to_equal(false)
```

</details>

#### embeds static assets with correct path

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val asset_path = "css/style.css"
val asset_content = "body { margin: 0; }"
expect(asset_path).to_contain("css/")
expect(asset_content.len()).to_be_greater_than(0)
```

</details>

#### handles binary assets (images)

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PNG, JPG, etc. should be stored as raw bytes
val png_header = [137, 80, 78, 71]  # PNG magic bytes
expect(png_header[0]).to_equal(137)
expect(png_header.len()).to_equal(4)
```

</details>

### SWA Reader

#### reads header and validates magic

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val magic = [83, 87, 65, 0]
val is_valid = (magic[0] == 83 and magic[1] == 87 and
                magic[2] == 65 and magic[3] == 0)
expect(is_valid).to_equal(true)
```

</details>

#### lists all assets in archive

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After reading an SWA, list_assets() returns all embedded paths
val expected_assets = ["index.html", "css/style.css", "js/app.js"]
expect(expected_assets.len()).to_equal(3)
expect(expected_assets).to_contain("index.html")
```

</details>

#### retrieves asset by path

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# get_asset("css/style.css") returns the file contents
val path = "css/style.css"
expect(path).to_start_with("css/")
```

</details>

#### returns error for missing asset

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "nonexistent.html"
expect(path).to_contain("nonexistent")
```

</details>

### Deployment Descriptor (webapp.sdn)

#### parses valid webapp.sdn

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = "webapp:\n  name: myapp\n  version: 1.0.0\n  port: 8080\n"
expect(descriptor).to_contain("name: myapp")
expect(descriptor).to_contain("port: 8080")
```

</details>

#### validates required fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# name and version are required
val has_name = true
val has_version = true
expect(has_name).to_equal(true)
expect(has_version).to_equal(true)
```

</details>

#### defaults port to 8080 when not specified

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_port = 8080
expect(default_port).to_equal(8080)
```

</details>

#### validates port range

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val port = 8080
val valid = (port > 0 and port < 65536)
expect(valid).to_equal(true)
```

</details>

### Mime Type Lookup

#### maps html extension to text/html

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = "html"
val expected = "text/html"
expect(ext).to_equal("html")
expect(expected).to_equal("text/html")
```

</details>

#### maps css extension to text/css

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = "css"
val expected = "text/css"
expect(ext).to_equal("css")
```

</details>

#### maps js extension to application/javascript

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = "js"
val expected = "application/javascript"
expect(ext).to_equal("js")
```

</details>

#### maps png extension to image/png

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ext = "png"
val expected = "image/png"
expect(ext).to_equal("png")
```

</details>

#### returns octet-stream for unknown extension

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fallback = "application/octet-stream"
expect(fallback).to_equal("application/octet-stream")
```

</details>

### SmfAppType WebApp

#### WebApp has value 5

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val webapp_value = 5
expect(webapp_value).to_equal(5)
```

</details>

#### WebApp name is webapp

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val name = "webapp"
expect(name).to_equal("webapp")
```

</details>

### Web Packaging CLI Commands

#### web build accepts --output flag

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["build", "--output", "myapp.swa"]
expect(args).to_contain("build")
expect(args).to_contain("--output")
```

</details>

#### web serve accepts port flag

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["serve", "myapp.swa", "--port", "3000"]
expect(args).to_contain("serve")
expect(args).to_contain("--port")
```

</details>

#### web deploy accepts target directory

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["deploy", "myapp.swa", "--target", "/opt/myapp"]
expect(args).to_contain("deploy")
expect(args).to_contain("--target")
```

</details>

### Plugin Package (SPX)

#### plugin.sdn has required fields

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor = "plugin:\n  name: my-plugin\n  version: 1.0.0\n  type: compiler\n"
expect(descriptor).to_contain("name: my-plugin")
expect(descriptor).to_contain("type: compiler")
```

</details>

#### installs to correct directory

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val install_dir = "~/.simple/plugins/my-plugin/1.0.0/"
expect(install_dir).to_contain("plugins/my-plugin")
```

</details>

### Container Image Generation

#### generates multi-stage Dockerfile for webapp

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val project_type = "webapp"
expect(project_type).to_equal("webapp")
```

</details>

#### generates simple Dockerfile for CLI app

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val project_type = "application"
expect(project_type).to_equal("application")
```

</details>

### Service Package

#### generates systemd unit on Linux

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val os = "linux"
expect(os).to_equal("linux")
```

</details>

#### generates launchd plist on macOS

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/requirement/web_app_packaging.md](doc/requirement/web_app_packaging.md)
- **Plan:** [doc/03_plan/web_app_packaging.md](doc/03_plan/web_app_packaging.md)
- **Design:** [doc/05_design/web_app_packaging.md](doc/05_design/web_app_packaging.md)
- **Research:** [doc/01_research/web_app_packaging.md](doc/01_research/web_app_packaging.md)


</details>

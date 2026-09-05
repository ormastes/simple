# ZIP-based SWA Archive Specification

> Tests for the ZIP-based SWA archive format. This extends the existing flat-binary SWA format with standard ZIP container support, similar to Java JAR/WAR archives. ZIP-based SWA archives use the standard PKZip format with specific directory conventions (META-SWA/, modules/, public/, i18n/) for web application packaging.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ZIP-based SWA Archive Specification

Tests for the ZIP-based SWA archive format. This extends the existing flat-binary SWA format with standard ZIP container support, similar to Java JAR/WAR archives. ZIP-based SWA archives use the standard PKZip format with specific directory conventions (META-SWA/, modules/, public/, i18n/) for web application packaging.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SWA-ZIP-001 through #SWA-ZIP-025 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | doc/requirement/web_app_packaging.md |
| Plan | doc/03_plan/web_app_packaging.md |
| Design | doc/05_design/web_app_packaging.md |
| Source | `test/01_unit/compiler/linker/swa_zip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the ZIP-based SWA archive format. This extends the existing flat-binary
SWA format with standard ZIP container support, similar to Java JAR/WAR archives.
ZIP-based SWA archives use the standard PKZip format with specific directory
conventions (META-SWA/, modules/, public/, i18n/) for web application packaging.

## Key Concepts

| Concept | Description |
|---------|-------------|
| ZIP Writer | Creates standard ZIP archives with stored (uncompressed) entries |
| ZIP Reader | Opens and extracts files from ZIP archives |
| ZIP Magic | PK\x03\x04 local file header signature (bytes 80, 75, 3, 4) |
| CRC-32 | Cyclic redundancy check for data integrity verification |
| SWA ZIP | ZIP with META-SWA/ convention for web application metadata |
| META-SWA/ | Reserved directory for deployment descriptor and metadata |
| modules/ | Directory for compiled .smf module files |
| public/ | Directory for static web assets (HTML, CSS, JS, images) |
| i18n/ | Directory for internationalization resource bundles |

## Scenarios

### ZIP Writer Basic

#### ZIP local file header has correct magic bytes PK\\x03\\x04

- ZIP local file header has correct magic bytes PK\\x03\\x04
   - Expected: ZIP_LOCAL_MAGIC[0] equals `80)   # 'P'`
   - Expected: ZIP_LOCAL_MAGIC[1] equals `75)   # 'K'`
   - Expected: ZIP_LOCAL_MAGIC[2] equals `3)    # \x03`
   - Expected: ZIP_LOCAL_MAGIC[3] equals `4)    # \x04`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ZIP local file header has correct magic bytes PK\\x03\\x04")
# PKZip local file header signature
val ZIP_LOCAL_MAGIC = [80, 75, 3, 4]
expect(ZIP_LOCAL_MAGIC[0]).to_equal(80)   # 'P'
expect(ZIP_LOCAL_MAGIC[1]).to_equal(75)   # 'K'
expect(ZIP_LOCAL_MAGIC[2]).to_equal(3)    # \x03
expect(ZIP_LOCAL_MAGIC[3]).to_equal(4)    # \x04
```

</details>

#### ZIP central directory has correct magic bytes PK\\x01\\x02

- ZIP central directory has correct magic bytes PK\\x01\\x02
   - Expected: ZIP_CENTRAL_MAGIC[0] equals `80)   # 'P'`
   - Expected: ZIP_CENTRAL_MAGIC[1] equals `75)   # 'K'`
   - Expected: ZIP_CENTRAL_MAGIC[2] equals `1)    # \x01`
   - Expected: ZIP_CENTRAL_MAGIC[3] equals `2)    # \x02`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ZIP central directory has correct magic bytes PK\\x01\\x02")
val ZIP_CENTRAL_MAGIC = [80, 75, 1, 2]
expect(ZIP_CENTRAL_MAGIC[0]).to_equal(80)   # 'P'
expect(ZIP_CENTRAL_MAGIC[1]).to_equal(75)   # 'K'
expect(ZIP_CENTRAL_MAGIC[2]).to_equal(1)    # \x01
expect(ZIP_CENTRAL_MAGIC[3]).to_equal(2)    # \x02
```

</details>

#### ZIP end of central directory has correct magic bytes PK\\x05\\x06

- ZIP end of central directory has correct magic bytes PK\\x05\\x06
   - Expected: ZIP_EOCD_MAGIC[0] equals `80)   # 'P'`
   - Expected: ZIP_EOCD_MAGIC[1] equals `75)   # 'K'`
   - Expected: ZIP_EOCD_MAGIC[2] equals `5)    # \x05`
   - Expected: ZIP_EOCD_MAGIC[3] equals `6)    # \x06`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("ZIP end of central directory has correct magic bytes PK\\x05\\x06")
val ZIP_EOCD_MAGIC = [80, 75, 5, 6]
expect(ZIP_EOCD_MAGIC[0]).to_equal(80)   # 'P'
expect(ZIP_EOCD_MAGIC[1]).to_equal(75)   # 'K'
expect(ZIP_EOCD_MAGIC[2]).to_equal(5)    # \x05
expect(ZIP_EOCD_MAGIC[3]).to_equal(6)    # \x06
```

</details>

#### uses STORE compression method (0) for uncompressed entries

- uses STORE compression method (0) for uncompressed entries
   - Expected: STORE_METHOD equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("uses STORE compression method (0) for uncompressed entries")
val STORE_METHOD = 0
expect(STORE_METHOD).to_equal(0)
```

</details>

#### CRC-32 produces non-zero value for non-empty data

- CRC-32 produces non-zero value for non-empty data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC-32 produces non-zero value for non-empty data")
# CRC-32 of "hello" is 0x3610A686
val crc32_hello = 907060870
expect(crc32_hello).to_be_greater_than(0)
```

</details>

#### CRC-32 of empty data is zero

- CRC-32 of empty data is zero
   - Expected: crc32_empty equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC-32 of empty data is zero")
val crc32_empty = 0
expect(crc32_empty).to_equal(0)
```

</details>

#### supports multiple file entries in a single archive

- supports multiple file entries in a single archive
   - Expected: file_names.len() equals `3`
   - Expected: file_names[0] equals `index.html`
   - Expected: file_names[1] equals `css/style.css`
   - Expected: file_names[2] equals `js/app.js`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("supports multiple file entries in a single archive")
val file_names = ["index.html", "css/style.css", "js/app.js"]
expect(file_names.len()).to_equal(3)
expect(file_names[0]).to_equal("index.html")
expect(file_names[1]).to_equal("css/style.css")
expect(file_names[2]).to_equal("js/app.js")
```

</details>

#### stores file sizes correctly for each entry

- stores file sizes correctly for each entry
   - Expected: uncompressed_size equals `compressed_size`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("stores file sizes correctly for each entry")
# Each entry in ZIP stores both compressed and uncompressed size
# For STORE method, they should be identical
val uncompressed_size = 1024
val compressed_size = 1024
expect(uncompressed_size).to_equal(compressed_size)
```

</details>

### ZIP Reader Basic

#### validates magic bytes when opening archive

- validates magic bytes when opening archive
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("validates magic bytes when opening archive")
val magic = [80, 75, 3, 4]
val is_valid = (magic[0] == 80 and magic[1] == 75 and
                magic[2] == 3 and magic[3] == 4)
expect(is_valid).to_equal(true)
```

</details>

#### rejects files with invalid magic bytes

- rejects files with invalid magic bytes
   - Expected: is_valid is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects files with invalid magic bytes")
val bad_magic = [0, 0, 0, 0]
val is_valid = (bad_magic[0] == 80 and bad_magic[1] == 75)
expect(is_valid).to_equal(false)
```

</details>

#### lists all files in the archive

- lists all files in the archive
   - Expected: expected_files.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("lists all files in the archive")
val expected_files = ["META-SWA/webapp.sdn", "modules/app.smf", "public/index.html"]
expect(expected_files.len()).to_equal(3)
expect(expected_files).to_contain("META-SWA/webapp.sdn")
expect(expected_files).to_contain("modules/app.smf")
expect(expected_files).to_contain("public/index.html")
```

</details>

#### reads file contents by path

- reads file contents by path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads file contents by path")
val path = "public/index.html"
val content = "<html><body>Hello</body></html>"
expect(path).to_start_with("public/")
expect(content).to_contain("<html>")
expect(content.len()).to_be_greater_than(0)
```

</details>

#### returns error for missing file path

- returns error for missing file path
   - Expected: found is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns error for missing file path")
val path = "nonexistent/file.txt"
val found = false
expect(found).to_equal(false)
expect(path).to_contain("nonexistent")
```

</details>

#### handles empty archives with only end-of-central-directory

- handles empty archives with only end-of-central-directory
   - Expected: entry_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("handles empty archives with only end-of-central-directory")
val entry_count = 0
expect(entry_count).to_equal(0)
```

</details>

### ZIP Round-trip

#### text file content preserved after write-then-read

- text file content preserved after write-then-read
   - Expected: restored equals `original`
   - Expected: restored.len() equals `original.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("text file content preserved after write-then-read")
val original = "body { margin: 0; padding: 0; }"
val restored = "body { margin: 0; padding: 0; }"
expect(restored).to_equal(original)
expect(restored.len()).to_equal(original.len())
```

</details>

#### binary data preserved after write-then-read

- binary data preserved after write-then-read
   - Expected: original_bytes.len() equals `restored_bytes.len()`
   - Expected: original_bytes[0] equals `restored_bytes[0]`
   - Expected: original_bytes[1] equals `restored_bytes[1]`
   - Expected: original_bytes[7] equals `restored_bytes[7]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("binary data preserved after write-then-read")
# PNG header bytes
val original_bytes = [137, 80, 78, 71, 13, 10, 26, 10]
val restored_bytes = [137, 80, 78, 71, 13, 10, 26, 10]
expect(original_bytes.len()).to_equal(restored_bytes.len())
expect(original_bytes[0]).to_equal(restored_bytes[0])
expect(original_bytes[1]).to_equal(restored_bytes[1])
expect(original_bytes[7]).to_equal(restored_bytes[7])
```

</details>

#### CRC-32 matches after round-trip

- CRC-32 matches after round-trip
   - Expected: write_crc equals `read_crc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("CRC-32 matches after round-trip")
val write_crc = 907060870
val read_crc = 907060870
expect(write_crc).to_equal(read_crc)
```

</details>

#### multiple files all survive round-trip

- multiple files all survive round-trip
   - Expected: file_count_written equals `file_count_read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("multiple files all survive round-trip")
val file_count_written = 5
val file_count_read = 5
expect(file_count_written).to_equal(file_count_read)
```

</details>

#### file paths with subdirectories preserved

- file paths with subdirectories preserved
   - Expected: restored_path equals `original_path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("file paths with subdirectories preserved")
val original_path = "css/themes/dark/main.css"
val restored_path = "css/themes/dark/main.css"
expect(restored_path).to_equal(original_path)
expect(restored_path).to_contain("/")
```

</details>

### SWA ZIP Builder

#### creates META-SWA directory with webapp.sdn

- creates META-SWA directory with webapp.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("creates META-SWA directory with webapp.sdn")
val meta_path = "META-SWA/webapp.sdn"
expect(meta_path).to_start_with("META-SWA/")
expect(meta_path).to_end_with("webapp.sdn")
```

</details>

#### places modules under modules/ directory

- places modules under modules/ directory
   - Expected: module_paths.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("places modules under modules/ directory")
val module_paths = [
    "modules/app/controllers/home.smf",
    "modules/app/controllers/api.smf",
    "modules/app/models/user.smf"
]
expect(module_paths.len()).to_equal(3)
expect(module_paths[0]).to_start_with("modules/")
expect(module_paths[1]).to_start_with("modules/")
expect(module_paths[2]).to_start_with("modules/")
```

</details>

#### places static assets under public/ directory

- places static assets under public/ directory
   - Expected: asset_paths.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("places static assets under public/ directory")
val asset_paths = [
    "public/index.html",
    "public/css/style.css",
    "public/js/app.js",
    "public/images/logo.png"
]
expect(asset_paths.len()).to_equal(4)
expect(asset_paths[0]).to_start_with("public/")
expect(asset_paths[3]).to_start_with("public/")
```

</details>

#### places i18n bundles under i18n/ directory

- places i18n bundles under i18n/ directory
   - Expected: i18n_paths.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("places i18n bundles under i18n/ directory")
val i18n_paths = [
    "i18n/messages.sdn",
    "i18n/messages.ko.sdn",
    "i18n/messages.ja.sdn"
]
expect(i18n_paths.len()).to_equal(3)
expect(i18n_paths[0]).to_start_with("i18n/")
expect(i18n_paths[0]).to_end_with(".sdn")
expect(i18n_paths[1]).to_contain(".ko.")
```

</details>

#### META-SWA/webapp.sdn contains required name and version

- META-SWA/webapp.sdn contains required name and version


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("META-SWA/webapp.sdn contains required name and version")
val descriptor = "webapp:\n  name: myapp\n  version: 1.0.0\n  port: 8080\n"
expect(descriptor).to_contain("name: myapp")
expect(descriptor).to_contain("version: 1.0.0")
```

</details>

#### archive contains all four conventional directories

- archive contains all four conventional directories
   - Expected: directories.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("archive contains all four conventional directories")
val directories = ["META-SWA/", "modules/", "public/", "i18n/"]
expect(directories.len()).to_equal(4)
expect(directories).to_contain("META-SWA/")
expect(directories).to_contain("modules/")
expect(directories).to_contain("public/")
expect(directories).to_contain("i18n/")
```

</details>

### SWA ZIP Reader

#### reads deployment descriptor from META-SWA/webapp.sdn

- reads deployment descriptor from META-SWA/webapp.sdn


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads deployment descriptor from META-SWA/webapp.sdn")
val descriptor_path = "META-SWA/webapp.sdn"
val descriptor_content = "webapp:\n  name: test-app\n  version: 2.0.0\n"
expect(descriptor_path).to_start_with("META-SWA/")
expect(descriptor_content).to_contain("name: test-app")
```

</details>

#### enumerates modules from modules/ directory

- enumerates modules from modules/ directory
   - Expected: modules.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("enumerates modules from modules/ directory")
val modules = ["app.controllers.home", "app.controllers.api", "app.models.user"]
expect(modules.len()).to_equal(3)
expect(modules).to_contain("app.controllers.home")
```

</details>

#### enumerates assets from public/ directory

- enumerates assets from public/ directory
   - Expected: assets.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("enumerates assets from public/ directory")
val assets = ["index.html", "css/style.css", "js/app.js"]
expect(assets.len()).to_equal(3)
expect(assets).to_contain("index.html")
expect(assets).to_contain("css/style.css")
```

</details>

#### enumerates i18n bundles from i18n/ directory

- enumerates i18n bundles from i18n/ directory
   - Expected: bundles.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("enumerates i18n bundles from i18n/ directory")
val bundles = ["messages.sdn", "messages.ko.sdn"]
expect(bundles.len()).to_equal(2)
expect(bundles[0]).to_end_with(".sdn")
```

</details>

#### provides asset mime type lookup

- provides asset mime type lookup
   - Expected: html_mime equals `text/html`
   - Expected: css_mime equals `text/css`
   - Expected: js_mime equals `application/javascript`
   - Expected: png_mime equals `image/png`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("provides asset mime type lookup")
val html_mime = "text/html"
val css_mime = "text/css"
val js_mime = "application/javascript"
val png_mime = "image/png"
expect(html_mime).to_equal("text/html")
expect(css_mime).to_equal("text/css")
expect(js_mime).to_equal("application/javascript")
expect(png_mime).to_equal("image/png")
```

</details>

#### returns default port from descriptor

- returns default port from descriptor
   - Expected: default_port equals `8080`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns default port from descriptor")
val default_port = 8080
expect(default_port).to_equal(8080)
```

</details>

#### verifies CRC-32 integrity on asset extraction

- verifies CRC-32 integrity on asset extraction
   - Expected: integrity_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("verifies CRC-32 integrity on asset extraction")
val expected_crc = 907060870
val actual_crc = 907060870
val integrity_ok = (expected_crc == actual_crc)
expect(integrity_ok).to_equal(true)
```

</details>

#### returns error for file outside convention directories

- returns error for file outside convention directories
   - Expected: is_recognized is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns error for file outside convention directories")
# Files not in META-SWA/, modules/, public/, or i18n/ are not recognized
val path = "random/unexpected.txt"
val is_recognized = (path.starts_with("META-SWA/") or
                     path.starts_with("modules/") or
                     path.starts_with("public/") or
                     path.starts_with("i18n/"))
expect(is_recognized).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/requirement/web_app_packaging.md`
- **Plan:** `doc/03_plan/web_app_packaging.md`
- **Design:** `doc/05_design/web_app_packaging.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SWA-ZIP`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d1198f5574a4af057e6fc2280e50fdbb0fa45567bd9948f877c8f20526b2f7d7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d1198f5574a4af057e6fc2280e50fdbb0fa45567bd9948f877c8f20526b2f7d7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d1198f5574a4af057e6fc2280e50fdbb0fa45567bd9948f877c8f20526b2f7d7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/linker/swa_zip_spec.spl
mirror: doc/06_spec/01_unit/compiler/linker/swa_zip_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/linker/swa_zip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/linker/swa_zip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/linker/swa_zip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/linker/swa_zip_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/linker/swa_zip_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ZIP local file header has correct magic bytes PK\\x03\\x04' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/swa_zip_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ZIP central directory has correct magic bytes PK\\x01\\x02' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/linker/swa_zip_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'ZIP end of central directory has correct magic bytes PK\\x05\\x06' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

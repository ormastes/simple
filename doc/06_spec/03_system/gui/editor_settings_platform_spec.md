# Editor Settings Platform Specification

> Tests covering platform_config_get_by_key, platform_config_set_by_key, simpleos_settings_schema, Platform category in full_settings_schema.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Settings Platform Specification

## Scenarios

### platform_config_get_by_key

#### exists in platform.spl

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exists in platform.spl
   - Expected: src contains `fn platform_config_get_by_key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exists in platform.spl")
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("fn platform_config_get_by_key")).to_equal(true)
```

</details>

#### accepts PlatformConfig and key text

- accepts PlatformConfig and key text
   - Expected: src contains `platform_config_get_by_key(config: PlatformConfig, key: text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts PlatformConfig and key text")
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("platform_config_get_by_key(config: PlatformConfig, key: text)")).to_equal(true)
```

</details>

### platform_config_set_by_key

#### exists in platform.spl

- exists in platform.spl
   - Expected: src contains `fn platform_config_set_by_key`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exists in platform.spl")
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("fn platform_config_set_by_key")).to_equal(true)
```

</details>

#### returns PlatformConfig

- returns PlatformConfig
   - Expected: src contains `platform_config_set_by_key(config: PlatformConfig, key: text, value: text) ->... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns PlatformConfig")
val src = read_text("src/lib/editor/00.common/platform.spl")
expect(src.contains("platform_config_set_by_key(config: PlatformConfig, key: text, value: text) -> PlatformConfig")).to_equal(true)
```

</details>

### simpleos_settings_schema

#### exists in simpleos_adapter.spl

- exists in simpleos_adapter.spl
   - Expected: src contains `fn simpleos_settings_schema`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("exists in simpleos_adapter.spl")
val src = read_text("src/app/editor/simpleos_adapter.spl")
expect(src.contains("fn simpleos_settings_schema")).to_equal(true)
```

</details>

#### returns filtered schema for simpleos platform

- returns filtered schema for simpleos platform
   - Expected: src contains `settings_filter_by_platform(full_settings_schema(), "simpleos")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns filtered schema for simpleos platform")
val src = read_text("src/app/editor/simpleos_adapter.spl")
expect(src.contains("settings_filter_by_platform(full_settings_schema(), \"simpleos\")")).to_equal(true)
```

</details>

### Platform category in full_settings_schema

#### settings_schema.spl contains Platform category descriptor

- settings_schema.spl contains Platform category descriptor
   - Expected: src contains `category: "Platform"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("settings_schema.spl contains Platform category descriptor")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("category: \"Platform\"")).to_equal(true)
```

</details>

#### max_open_files setting exists in schema

- max_open_files setting exists in schema
   - Expected: src contains `key: "max_open_files"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("max_open_files setting exists in schema")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"max_open_files\"")).to_equal(true)
```

</details>

#### file_watcher_enabled is desktop-only in schema

- file_watcher_enabled is desktop-only in schema
   - Expected: src contains `key: "file_watcher_enabled"`
   - Expected: src contains `key: "file_watcher_debounce_ms"`
   - Expected: src contains `key: "file_watcher_ignore_globs"`
   - Expected: src contains `platform: "desktop"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("file_watcher_enabled is desktop-only in schema")
val src = read_text("src/lib/editor/00.common/settings_schema.spl")
expect(src.contains("key: \"file_watcher_enabled\"")).to_equal(true)
expect(src.contains("key: \"file_watcher_debounce_ms\"")).to_equal(true)
expect(src.contains("key: \"file_watcher_ignore_globs\"")).to_equal(true)
expect(src.contains("platform: \"desktop\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_settings_platform_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering platform_config_get_by_key, platform_config_set_by_key, simpleos_settings_schema, Platform category in full_settings_schema.
- platform_config_get_by_key
- platform_config_set_by_key
- simpleos_settings_schema
- Platform category in full_settings_schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b3a0bdd3757a061d805e221750c6505c198e4a7fc8d62e19821b7254bf3915f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b3a0bdd3757a061d805e221750c6505c198e4a7fc8d62e19821b7254bf3915f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b3a0bdd3757a061d805e221750c6505c198e4a7fc8d62e19821b7254bf3915f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gui/editor_settings_platform_spec.spl
mirror: doc/06_spec/03_system/gui/editor_settings_platform_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/editor_settings_platform_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/editor_settings_platform_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/editor_settings_platform_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exists in platform.spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_settings_platform_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts PlatformConfig and key text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/editor_settings_platform_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exists in platform.spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

# Launcher Composition Specification

> Tests covering launcher SCI application projection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Launcher Composition Specification

## Scenarios

### launcher SCI application projection

#### REQ-008 projects renamed application metadata into one launcher process

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REQ-008 projects renamed application metadata into one launcher process
   - Expected: first_load.ok is true
   - Expected: first_load.code equals `SCI_LAUNCHER_OK`
   - Expected: second_load.ok is true
   - Expected: app_count equals `before_count + 1`
   - Expected: _app_index_by_name("Notes") equals `-1`
   - Expected: renamed >= 0 is true
   - Expected: _app_path(renamed) equals `/sys/apps/notes.smf`
   - Expected: composition_app_ids_v1[0] equals `notes`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REQ-008 projects renamed application metadata into one launcher process")
val first = _image("schema: simple.composition/1\napps:\n  - id: notes\n    name: Notes\n    artifact: /sys/apps/notes.smf\n")
val second = _image("schema: simple.composition/1\napps:\n  - id: notes\n    name: Knowledge Notes\n    artifact: /sys/apps/notes.smf\n")

launcher_init()
val before_count = app_count
val first_load = launcher_load_composition_bytes_v1(first.bytes)
val second_load = launcher_load_composition_bytes_v1(second.bytes)

expect(first_load.ok).to_equal(true)
expect(first_load.code).to_equal("SCI_LAUNCHER_OK")
expect(second_load.ok).to_equal(true)
expect(app_count).to_equal(before_count + 1)
expect(_app_index_by_name("Notes")).to_equal(-1)
val renamed = _app_index_by_name("Knowledge Notes")
expect(renamed >= 0).to_equal(true)
expect(_app_path(renamed)).to_equal("/sys/apps/notes.smf")
expect(composition_app_ids_v1[0]).to_equal("notes")
```

</details>

#### REQ-008 removes an application omitted by the replacement image

- REQ-008 removes an application omitted by the replacement image
   - Expected: first_load.ok is true
   - Expected: second_load.ok is true
   - Expected: _app_index_by_name("Notes Removal Fixture") equals `-1`
   - Expected: _app_index_by_name("Tasks Retained Fixture") >= 0 is true
   - Expected: app_count equals `before_count + 1`
   - Expected: composition_app_ids_v1.len() equals `1`
   - Expected: composition_app_ids_v1[0] equals `tasks`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REQ-008 removes an application omitted by the replacement image")
val first = _image("schema: simple.composition/1\napps:\n  - id: notes\n    name: Notes Removal Fixture\n    artifact: /sys/apps/notes_remove.smf\n  - id: tasks\n    name: Tasks Retained Fixture\n    artifact: /sys/apps/tasks_retain.smf\n")
val second = _image("schema: simple.composition/1\napps:\n  - id: tasks\n    name: Tasks Retained Fixture\n    artifact: /sys/apps/tasks_retain.smf\n")

launcher_init()
val before_count = app_count
val first_load = launcher_load_composition_bytes_v1(first.bytes)
val second_load = launcher_load_composition_bytes_v1(second.bytes)

expect(first_load.ok).to_equal(true)
expect(second_load.ok).to_equal(true)
expect(_app_index_by_name("Notes Removal Fixture")).to_equal(-1)
expect(_app_index_by_name("Tasks Retained Fixture") >= 0).to_equal(true)
expect(app_count).to_equal(before_count + 1)
expect(composition_app_ids_v1.len()).to_equal(1)
expect(composition_app_ids_v1[0]).to_equal("tasks")
```

</details>

#### REQ-003 projects a validated shortcut through the launcher owner API

- REQ-003 projects a validated shortcut through the launcher owner API
   - Expected: result.ok is true
   - Expected: index >= 0 is true
   - Expected: _app_key(index.to_u64()) equals `69u32`
   - Expected: _app_mod(index.to_u64()) equals `MOD_CTRL | MOD_META`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REQ-003 projects a validated shortcut through the launcher owner API")
val shortcut_image = _image("schema: simple.composition/1\napps:\n  - id: editor-shortcut\n    name: Shortcut Editor\n    artifact: /sys/apps/shortcut_editor.smf\n    shortcut: Ctrl+Meta+E\n")
launcher_init()
val result = launcher_load_composition_bytes_v1(shortcut_image.bytes)
val index = _app_index_by_name("Shortcut Editor")
expect(result.ok).to_equal(true)
expect(index >= 0).to_equal(true)
expect(_app_key(index.to_u64())).to_equal(69u32)
expect(_app_mod(index.to_u64())).to_equal(MOD_CTRL | MOD_META)
```

</details>

#### REQ-003 rejects malformed shortcuts before changing the registry

- REQ-003 rejects malformed shortcuts before changing the registry
   - Expected: result.ok is false
   - Expected: result.code equals `SCI_LAUNCHER_SHORTCUT_INVALID`
   - Expected: app_count equals `before_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REQ-003 rejects malformed shortcuts before changing the registry")
val shortcut_image = _image("schema: simple.composition/1\napps:\n  - id: bad-shortcut\n    name: Bad Shortcut\n    artifact: /sys/apps/bad_shortcut.smf\n    shortcut: Meta+Enter\n")
launcher_init()
val before_count = app_count
val result = launcher_load_composition_bytes_v1(shortcut_image.bytes)
expect(result.ok).to_equal(false)
expect(result.code).to_equal("SCI_LAUNCHER_SHORTCUT_INVALID")
expect(app_count).to_equal(before_count)
```

</details>

#### REQ-003 fails closed when manifest capability projection is unavailable

- REQ-003 fails closed when manifest capability projection is unavailable
   - Expected: result.ok is false
   - Expected: result.code equals `SCI_LAUNCHER_MANIFEST_CAPABILITY_PROJECTION_REQUIRED`
   - Expected: app_count equals `before_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REQ-003 fails closed when manifest capability projection is unavailable")
val policy_image = _image("schema: simple.composition/1\napps:\n  - id: editor-policy\n    name: Policy Editor\n    artifact: /sys/apps/policy_editor.smf\n    capabilities: [FileRead(/)]\n")
launcher_init()
val before_count = app_count
val result = launcher_load_composition_bytes_v1(policy_image.bytes)
expect(result.ok).to_equal(false)
expect(result.code).to_equal("SCI_LAUNCHER_MANIFEST_CAPABILITY_PROJECTION_REQUIRED")
expect(app_count).to_equal(before_count)
```

</details>

#### REQ-008 fails closed when the association owner has no projection API

- REQ-008 fails closed when the association owner has no projection API
   - Expected: result.ok is false
   - Expected: result.code equals `SCI_LAUNCHER_ASSOCIATION_PROJECTION_REQUIRED`
   - Expected: app_count equals `before_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("REQ-008 fails closed when the association owner has no projection API")
val association_image = _image("schema: simple.composition/1\napps:\n  - id: notes-association\n    name: Associated Notes\n    artifact: /sys/apps/associated_notes.smf\n    associations: [.notes]\n")
launcher_init()
val before_count = app_count
val result = launcher_load_composition_bytes_v1(association_image.bytes)
expect(result.ok).to_equal(false)
expect(result.code).to_equal("SCI_LAUNCHER_ASSOCIATION_PROJECTION_REQUIRED")
expect(app_count).to_equal(before_count)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/launcher/launcher_composition_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering launcher SCI application projection.
- launcher SCI application projection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `7fbeef4790bdbb7da9df49ac2a3be8048f3ec3632a23eeb8509185845e1bf80c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7fbeef4790bdbb7da9df49ac2a3be8048f3ec3632a23eeb8509185845e1bf80c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7fbeef4790bdbb7da9df49ac2a3be8048f3ec3632a23eeb8509185845e1bf80c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/services/launcher/launcher_composition_spec.spl
mirror: doc/06_spec/01_unit/os/services/launcher/launcher_composition_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/launcher/launcher_composition_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/launcher/launcher_composition_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/launcher/launcher_composition_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/launcher/launcher_composition_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-008 projects renamed application metadata into one launcher process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/launcher/launcher_composition_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-008 removes an application omitted by the replacement image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/launcher/launcher_composition_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REQ-003 projects a validated shortcut through the launcher owner API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

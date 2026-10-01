# Launcher App Launch Consumer Specification

> Tests covering REQ-008 SimpleAppLaunchV1 launcher consumer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Launcher App Launch Consumer Specification

## Scenarios

### REQ-008 SimpleAppLaunchV1 launcher consumer

#### encodes the admitted SCI record into a canonical fixed-width arena

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-008
```

</details>

#### re-resolves stable app ID after metadata and artifact reload

- re-resolves stable app ID after metadata and artifact reload
   - Expected: app_pid[new_slot] equals `4200u64`
   - Expected: app_launch_state[new_slot] equals `running`
   - Expected: app_launch_count[new_slot] equals `9u64`
   - Expected: process_app_index[0] equals `new_slot.to_i64()`
   - Expected: process_app_id[0] equals `notes-stable`
   - Expected: stale.status equals `SCI_APP_LAUNCH_ARTIFACT_STALE`
   - Expected: current_plan.artifact_path equals `/sys/apps/notes_after.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("re-resolves stable app ID after metadata and artifact reload")
launcher_init()
expect(_load_app("schema: simple.composition/1\napps:\n  - id: notes-stable\n    name: Notes Before\n    artifact: /sys/apps/notes_before.smf\n")).to_be(true)
val old_request = launcher_prepare_composition_app_launch_v1("notes-stable", [])
expect(old_request.ok).to_be(true)
val old_slot = _app_index_by_name("Notes Before").to_u64()
app_pid[old_slot] = 4200
app_launch_state[old_slot] = "running"
app_launch_count[old_slot] = 9
process_app_index[0] = old_slot.to_i64()
process_app_id[0] = "/sys/apps/notes_before.smf"
process_active[0] = true

expect(_load_app("schema: simple.composition/1\napps:\n  - id: notes-stable\n    name: Notes After\n    artifact: /sys/apps/notes_after.smf\n")).to_be(true)
val new_slot = _app_index_by_name("Notes After").to_u64()
expect(app_pid[new_slot]).to_equal(4200u64)
expect(app_launch_state[new_slot]).to_equal("running")
expect(app_launch_count[new_slot]).to_equal(9u64)
expect(process_app_index[0]).to_equal(new_slot.to_i64())
expect(process_app_id[0]).to_equal("notes-stable")

val stale = launcher_validate_app_launch_arena_v1(old_request.request.bytes)
expect(stale.ok).to_be(false)
expect(stale.status).to_equal(SCI_APP_LAUNCH_ARTIFACT_STALE)
val current = launcher_prepare_composition_app_launch_v1("notes-stable", [])
expect(current.ok).to_be(true)
val current_plan = launcher_validate_app_launch_arena_v1(current.request.bytes)
expect(current_plan.ok).to_be(true)
expect(current_plan.artifact_path).to_equal("/sys/apps/notes_after.smf")
```

</details>

#### rejects non-canonical offsets and unsupported actions before spawn

- rejects non-canonical offsets and unsupported actions before spawn
   - Expected: unsupported.status equals `SCI_APP_LAUNCH_ACTION_UNSUPPORTED`
   - Expected: malformed.status equals `SCI_APP_LAUNCH_REQUEST_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects non-canonical offsets and unsupported actions before spawn")
val encoded = encode_launcher_app_launch_v1(
    "notes", "/sys/apps/notes.smf", "inspect", [], [],
)
expect(encoded.ok).to_be(true)
val unsupported = launcher_validate_app_launch_arena_v1(encoded.bytes)
expect(unsupported.ok).to_be(false)
expect(unsupported.status).to_equal(SCI_APP_LAUNCH_ACTION_UNSUPPORTED)

var corrupt = encoded.bytes
corrupt[4] = 31u8
val malformed = launcher_validate_app_launch_arena_v1(corrupt)
expect(malformed.ok).to_be(false)
expect(malformed.status).to_equal(SCI_APP_LAUNCH_REQUEST_INVALID)
```

</details>

#### fails closed on capability words until scoped manifest projection exists

- fails closed on capability words until scoped manifest projection exists
   - Expected: plan.status equals `SCI_APP_LAUNCH_SCOPED_CAPABILITY_REQUIRED`
   - Expected: plan.code equals `SCI_APP_LAUNCH_MANIFEST_CAPABILITY_PROJECTION_REQUIRED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed on capability words until scoped manifest projection exists")
launcher_init()
expect(_load_app("schema: simple.composition/1\napps:\n  - id: notes-cap\n    name: Notes Capability\n    artifact: /sys/apps/notes_cap.smf\n")).to_be(true)
val encoded = encode_launcher_app_launch_v1(
    "notes-cap", "/sys/apps/notes_cap.smf", "launch", [], [1u64],
)
val plan = launcher_validate_app_launch_arena_v1(encoded.bytes)
expect(plan.ok).to_be(false)
expect(plan.status).to_equal(SCI_APP_LAUNCH_SCOPED_CAPABILITY_REQUIRED)
expect(plan.code).to_equal("SCI_APP_LAUNCH_MANIFEST_CAPABILITY_PROJECTION_REQUIRED")
```

</details>

#### rejects artifacts outside the launcher recipe and known manifest kinds

- rejects artifacts outside the launcher recipe and known manifest kinds
   - Expected: outside_plan.status equals `SCI_APP_LAUNCH_MANIFEST_REJECTED`
   - Expected: outside_plan.code equals `SCI_APP_LAUNCH_RECIPE_SCOPE_REJECTED`
   - Expected: unknown_plan.status equals `SCI_APP_LAUNCH_MANIFEST_REJECTED`
   - Expected: unknown_plan.code equals `SCI_APP_LAUNCH_ARTIFACT_KIND_UNSUPPORTED`
   - Expected: launcher_launch("Unknown Kind") equals `-1`
   - Expected: app_launch_state[unknown_slot] equals `idle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects artifacts outside the launcher recipe and known manifest kinds")
launcher_init()
expect(_load_app("schema: simple.composition/1\napps:\n  - id: outside-app\n    name: Outside App\n    artifact: /tmp/outside.smf\n")).to_be(true)
val outside = launcher_prepare_composition_app_launch_v1("outside-app", [])
val outside_plan = launcher_validate_app_launch_arena_v1(outside.request.bytes)
expect(outside_plan.ok).to_be(false)
expect(outside_plan.status).to_equal(SCI_APP_LAUNCH_MANIFEST_REJECTED)
expect(outside_plan.code).to_equal("SCI_APP_LAUNCH_RECIPE_SCOPE_REJECTED")

expect(_load_app("schema: simple.composition/1\napps:\n  - id: unknown-kind\n    name: Unknown Kind\n    artifact: /sys/apps/unknown.txt\n")).to_be(true)
val unknown = launcher_prepare_composition_app_launch_v1("unknown-kind", [])
val unknown_plan = launcher_validate_app_launch_arena_v1(unknown.request.bytes)
expect(unknown_plan.ok).to_be(false)
expect(unknown_plan.status).to_equal(SCI_APP_LAUNCH_MANIFEST_REJECTED)
expect(unknown_plan.code).to_equal("SCI_APP_LAUNCH_ARTIFACT_KIND_UNSUPPORTED")
val unknown_slot = _app_index_by_name("Unknown Kind").to_u64()
expect(launcher_launch("Unknown Kind")).to_equal(-1)
expect(app_launch_state[unknown_slot]).to_equal("idle")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REQ-008 SimpleAppLaunchV1 launcher consumer.
- REQ-008 SimpleAppLaunchV1 launcher consumer

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

- `REQ-SSPEC-OS`
- `REQ-008`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fdd420ce8cc3eb1337f9ab159ff65950f47331fd332a0bd4ea3afee5f822cee7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fdd420ce8cc3eb1337f9ab159ff65950f47331fd332a0bd4ea3afee5f822cee7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fdd420ce8cc3eb1337f9ab159ff65950f47331fd332a0bd4ea3afee5f822cee7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl
mirror: doc/06_spec/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl:42:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'encodes the admitted SCI record into a canonical fixed-width arena' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-resolves stable app ID after metadata and artifact reload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-canonical offsets and unsupported actions before spawn' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on capability words until scoped manifest projection exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

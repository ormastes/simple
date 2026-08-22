# launcher_app_launch_consumer_spec

> Verifies the launcher app launch consumer behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# launcher_app_launch_consumer_spec

Verifies the launcher app launch consumer behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the launcher app launch consumer behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### REQ-008 SimpleAppLaunchV1 launcher consumer

#### encodes the admitted SCI record into a canonical fixed-width arena

- Verify: encodes the admitted SCI record into a canonical fixed-width arena
   - Expected: prepared.request.descriptor.descriptor_size equals `SIMPLE_APP_LAUNCH_V1_SIZE`
   - Expected: decoded.app_id equals `notes-launch`
   - Expected: decoded.artifact_id equals `/sys/apps/notes_launch.smf`
   - Expected: decoded.action_id equals `launch`
   - Expected: decoded.args equals `["/tmp/readme.notes"]`
   - Expected: decoded.capability_words.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: plan.status equals `SCI_APP_LAUNCH_OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-008
step("Verify: encodes the admitted SCI record into a canonical fixed-width arena")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
launcher_init()
expect(_load_app("schema: simple.composition/1\napps:\n  - id: notes-launch\n    name: Notes Launch\n    artifact: /sys/apps/notes_launch.smf\n")).to_be(true)

val prepared = launcher_prepare_composition_app_launch_v1(
    "notes-launch", ["/tmp/readme.notes"],
)
expect(prepared.ok).to_be(true)
expect(prepared.request.descriptor.descriptor_size).to_equal(SIMPLE_APP_LAUNCH_V1_SIZE)
val decoded = decode_launcher_app_launch_v1(prepared.request.bytes)
expect(decoded.ok).to_be(true)
expect(decoded.app_id).to_equal("notes-launch")
expect(decoded.artifact_id).to_equal("/sys/apps/notes_launch.smf")
expect(decoded.action_id).to_equal("launch")
expect(decoded.args).to_equal(["/tmp/readme.notes"])
expect(decoded.capability_words.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario

val plan = launcher_validate_app_launch_arena_v1(prepared.request.bytes)
expect(plan.ok).to_be(true)
expect(plan.status).to_equal(SCI_APP_LAUNCH_OK)
expect(plan.manifest_identity).to_contain("kind=smf")
expect(plan.manifest_identity).to_contain("entry=/sys/apps/notes_launch.smf")
```

</details>

#### re-resolves stable app ID after metadata and artifact reload

- Verify: re-resolves stable app ID after metadata and artifact reload
   - Expected: app_pid[new_slot] equals `4200u64`
   - Expected: app_launch_state[new_slot] equals `running`
   - Expected: app_launch_count[new_slot] equals `9u64`
   - Expected: process_app_index[0] equals `new_slot.to_i64()`
   - Expected: process_app_id[0] equals `notes-stable`
   - Expected: stale.status equals `SCI_APP_LAUNCH_ARTIFACT_STALE`
   - Expected: current_plan.artifact_path equals `/sys/apps/notes_after.smf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-008
step("Verify: re-resolves stable app ID after metadata and artifact reload")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects non-canonical offsets and unsupported actions before spawn
   - Expected: unsupported.status equals `SCI_APP_LAUNCH_ACTION_UNSUPPORTED`
   - Expected: malformed.status equals `SCI_APP_LAUNCH_REQUEST_INVALID`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-008
step("Verify: rejects non-canonical offsets and unsupported actions before spawn")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: fails closed on capability words until scoped manifest projection exists
   - Expected: plan.status equals `SCI_APP_LAUNCH_SCOPED_CAPABILITY_REQUIRED`
   - Expected: plan.code equals `SCI_APP_LAUNCH_MANIFEST_CAPABILITY_PROJECTION_REQUIRED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-008
step("Verify: fails closed on capability words until scoped manifest projection exists")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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

- Verify: rejects artifacts outside the launcher recipe and known manifest kinds
   - Expected: outside_plan.status equals `SCI_APP_LAUNCH_MANIFEST_REJECTED`
   - Expected: outside_plan.code equals `SCI_APP_LAUNCH_RECIPE_SCOPE_REJECTED`
   - Expected: unknown_plan.status equals `SCI_APP_LAUNCH_MANIFEST_REJECTED`
   - Expected: unknown_plan.code equals `SCI_APP_LAUNCH_ARTIFACT_KIND_UNSUPPORTED`
   - Expected: launcher_launch("Unknown Kind") equals `-1)  # oracle: pinned constant asserted by this scenario`
   - Expected: app_launch_state[unknown_slot] equals `idle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-008
step("Verify: rejects artifacts outside the launcher recipe and known manifest kinds")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
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
expect(launcher_launch("Unknown Kind")).to_equal(-1)  # oracle: pinned constant asserted by this scenario
expect(app_launch_state[unknown_slot]).to_equal("idle")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b31d642f74af1c400d9ca50ce8c79d112d401df3e0db06b1cf18b03a8e0504f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b31d642f74af1c400d9ca50ce8c79d112d401df3e0db06b1cf18b03a8e0504f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b31d642f74af1c400d9ca50ce8c79d112d401df3e0db06b1cf18b03a8e0504f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.spl
mirror: doc/06_spec/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/launcher/launcher_app_launch_consumer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

# debug_doctor_matrix_spec

> debug-doctor capability matrix unit spec (P11).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# debug_doctor_matrix_spec

debug-doctor capability matrix unit spec (P11).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

debug-doctor capability matrix unit spec (P11).

The doctor is the acceptance test for "does this host properly support DAP
and profile", so this spec checks that its cells are PRODUCED, not declared:

  * the `ref` row constructs a real RefDebugSession, attaches, acquires the
    group through the SINGLE accessor `ref_debug_profiler(session)` (NOT by
    pairing `debug()` + `profile()`, which diverges because classes are
    value types), and reports what the accessors answer. Its step count is
    asserted EXACT against the fixture's known instruction count, so the row
    cannot pass while reporting a fabricated number.
  * the host profile cell comes from an elapsed time really measured here,
    with unmeasured quantities held at PROFILE_ABSENT (-1) and rendered as
    `-` — never as a zero that could be mistaken for a measurement.
  * level decoding is FAIL-CLOSED: an unrecognised tier name in the registry
    decodes to Unavailable, so a typo can never read as a working capability.
  * GPU rows are host-aware: a fake probe drives the deterministic cases,
    and the live-host assertions accept ok OR a stated skip reason but never
    an empty or invented one.
  * Metal on a non-macOS host must SKIP, with its own reason
    ("skip:metal-unavailable-not-macos" from metal_lane_session.spl:149).
    That skip is correct and is asserted as correct — never fixed up, never
    replaced with a fabricated Metal result.

Design: doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md §1.5, §5
Plan:   doc/03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md (P11)

## Scenarios

### debug-doctor — the ref row really constructs a session and calls accessors

#### attaches the ref lane and acquires the group through one accessor

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- attaches the ref lane and acquires the group through one accessor
   - Expected: row.target equals `ref`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("attaches the ref lane and acquires the group through one accessor")
val row = ref_row()
expect(row.target).to_equal("ref")
assert_true(row_is_attachable(row))
# The group acquired, so the accessors answered.
assert_true(row_can_debug(row))
```

</details>

#### reports the debug level the ref target itself answers

- reports the debug level the ref target itself answers
   - Expected: cap_level_name(row.debug_level) equals `native`
   - Expected: row_debug_cell(row) equals `native (svmg_pc)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports the debug level the ref target itself answers")
val row = ref_row()
expect(cap_level_name(row.debug_level)).to_equal("native")
expect(row_debug_cell(row)).to_equal("native (svmg_pc)")
```

</details>

#### reports an EXACT emulated step count from a real run

- reports an EXACT emulated step count from a real run
   - Expected: cap_level_name(row.profile.level) equals `emulated`
   - Expected: row.profile.steps equals `DOCTOR_REF_EXPECTED_STEPS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports an EXACT emulated step count from a real run")
val row = ref_row()
expect(cap_level_name(row.profile.level)).to_equal("emulated")
assert_true(profile_has_steps(row.profile))
# Exact, not "greater than zero": a fabricated or drifting counter
# fails this.
expect(row.profile.steps).to_equal(DOCTOR_REF_EXPECTED_STEPS)
```

</details>

#### reports no device timer for the ref lane rather than a zero

- reports no device timer for the ref lane rather than a zero
   - Expected: row.profile.device_ns equals `PROFILE_ABSENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports no device timer for the ref lane rather than a zero")
val row = ref_row()
expect(row.profile.device_ns).to_equal(PROFILE_ABSENT)
assert_false(profile_has_device_time(row.profile))
```

</details>

### debug-doctor — host row is measured, not declared

#### measures a positive wall interval with the host clock

- measures a positive wall interval with the host clock


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("measures a positive wall interval with the host clock")
val wall_ns = measure_host_wall_ns()
# A real elapsed measurement over real work; PROFILE_ABSENT if the
# clock never advanced. The assertion is on the measurement.
assert_true(wall_ns > 0)
```

</details>

#### reports host profile as native wall carrying the measured value

- reports host profile as native wall carrying the measured value
   - Expected: row.target equals `host`
   - Expected: cap_level_name(row.profile.level) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports host profile as native wall carrying the measured value")
val row = host_row(empty_registry(), "")
expect(row.target).to_equal("host")
assert_true(row_is_attachable(row))
expect(cap_level_name(row.profile.level)).to_equal("native")
assert_true(row.profile.wall_ns > 0)
```

</details>

#### surfaces absent host quantities as PROFILE_ABSENT, never zero

- surfaces absent host quantities as PROFILE_ABSENT, never zero
   - Expected: row.profile.device_ns equals `PROFILE_ABSENT`
   - Expected: row.profile.steps equals `PROFILE_ABSENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("surfaces absent host quantities as PROFILE_ABSENT, never zero")
val row = host_row(empty_registry(), "")
# A host has no device timer, and `steps` needs P4's interpreter
# counter. Both must be absent, not 0.
expect(row.profile.device_ns).to_equal(PROFILE_ABSENT)
expect(row.profile.steps).to_equal(PROFILE_ABSENT)
assert_false(profile_has_steps(row.profile))
# And they must RENDER as '-', so a glance cannot misread them.
val summary = profile_report_summary(row.profile)
assert_true(summary.contains("device=-"))
assert_true(summary.contains("steps=-"))
```

</details>

#### does not claim a host DebugTarget while none is registered

- does not claim a host DebugTarget while none is registered
   - Expected: cap_level_name(row.debug_level) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not claim a host DebugTarget while none is registered")
val row = host_row(empty_registry(), "")
expect(cap_level_name(row.debug_level)).to_equal("unavailable")
assert_false(row_can_debug(row))
assert_true(row.debug_detail.contains("host_debug_target.spl"))
```

</details>

#### skips attach when the named program does not exist

- skips attach when the named program does not exist


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips attach when the named program does not exist")
val row = host_row(empty_registry(), "no/such/program_p11.spl")
assert_true(row.attach.starts_with("skip:host-program-not-found"))
assert_false(row_is_attachable(row))
```

</details>

### debug-doctor — registry decoding is fail-closed

#### reports a registered host DebugTarget instead of the pending note

- reports a registered host DebugTarget instead of the pending note
   - Expected: row_debug_cell(row) equals `native (line)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a registered host DebugTarget instead of the pending note")
var registry = CapabilityRegistry.create()
registry.register(RegisteredCapability(
    target: "host", debug_level: "native", debug_detail: "line",
    profile_level: "native", profile_detail: "wall+steps"))
val row = host_row(registry, "")
expect(row_debug_cell(row)).to_equal("native (line)")
assert_true(row_can_debug(row))
```

</details>

#### decodes an unrecognised tier name to unavailable, not to a guess

- decodes an unrecognised tier name to unavailable, not to a guess
   - Expected: cap_level_name(row.debug_level) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes an unrecognised tier name to unavailable, not to a guess")
var registry = CapabilityRegistry.create()
registry.register(RegisteredCapability(
    target: "host", debug_level: "NATIVE-ish", debug_detail: "line",
    profile_level: "supercharged", profile_detail: "x"))
val row = host_row(registry, "")
# Fail-closed: a typo or a newer backend's unknown spelling must
# never read as a working capability.
expect(cap_level_name(row.debug_level)).to_equal("unavailable")
assert_false(row_can_debug(row))
```

</details>

#### reports a registered GPU DebugTarget on an attachable backend

- reports a registered GPU DebugTarget on an attachable backend
   - Expected: row_debug_cell(row) equals `native (svmg_pc)`
   - Expected: cap_level_name(row.profile.level) equals `emulated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a registered GPU DebugTarget on an attachable backend")
var registry = CapabilityRegistry.create()
registry.register(RegisteredCapability(
    target: "cuda", debug_level: "native", debug_detail: "svmg_pc",
    profile_level: "emulated", profile_detail: "steps"))
var probe = StubProbe.with_available(["cuda"])
val row = gpu_row(registry, "cuda", probe)
assert_true(row_is_attachable(row))
expect(row_debug_cell(row)).to_equal("native (svmg_pc)")
expect(cap_level_name(row.profile.level)).to_equal("emulated")
```

</details>

#### never prints capabilities for a backend that did not attach

- never prints capabilities for a backend that did not attach
   - Expected: row.attach equals `skip:cuda-driver-unavailable`
   - Expected: cap_level_name(row.debug_level) equals `unavailable`
   - Expected: cap_level_name(row.profile.level) equals `unavailable`
   - Expected: row.profile.steps equals `PROFILE_ABSENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never prints capabilities for a backend that did not attach")
var registry = CapabilityRegistry.create()
# Registered, but the hardware is absent: the row must still show the
# skip and no capability, because it cannot be exercised here.
registry.register(RegisteredCapability(
    target: "cuda", debug_level: "native", debug_detail: "svmg_pc",
    profile_level: "native", profile_detail: "cuEvent"))
var probe = StubProbe.with_available([])
val row = gpu_row(registry, "cuda", probe)
expect(row.attach).to_equal("skip:cuda-driver-unavailable")
expect(cap_level_name(row.debug_level)).to_equal("unavailable")
expect(cap_level_name(row.profile.level)).to_equal("unavailable")
expect(row.profile.steps).to_equal(PROFILE_ABSENT)
```

</details>

### debug-doctor — matrix shape and rendering

#### emits host, ref, then one row per GPU backend in a fixed order

- emits host, ref, then one row per GPU backend in a fixed order
   - Expected: rows.len() equals `5`
   - Expected: rows[0].target equals `host`
   - Expected: rows[1].target equals `ref`
   - Expected: rows[2].target equals `cuda`
   - Expected: rows[3].target equals `vulkan`
   - Expected: rows[4].target equals `metal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits host, ref, then one row per GPU backend in a fixed order")
var probe = StubProbe.with_available(["cuda"])
val rows = doctor_rows(empty_registry(), probe, "")
expect(rows.len()).to_equal(5)
expect(rows[0].target).to_equal("host")
expect(rows[1].target).to_equal("ref")
expect(rows[2].target).to_equal("cuda")
expect(rows[3].target).to_equal("vulkan")
expect(rows[4].target).to_equal("metal")
```

</details>

#### renders a header and one line per row without truncating reasons

- renders a header and one line per row without truncating reasons
   - Expected: lines.len() equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders a header and one line per row without truncating reasons")
var probe = StubProbe.with_available([])
val rows = doctor_rows(empty_registry(), probe, "")
val rendered = render_doctor_matrix(rows)
val lines = rendered.split("\n")
expect(lines.len()).to_equal(6)
assert_true(lines[0].contains("target"))
assert_true(lines[0].contains("attach"))
assert_true(lines[0].contains("debug"))
assert_true(lines[0].contains("profile"))
# The full skip reason survives into the rendered cell.
assert_true(rendered.contains("skip:metal-unavailable-not-macos"))
```

</details>

#### explains every unavailable cell in the detail lines

- explains every unavailable cell in the detail lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("explains every unavailable cell in the detail lines")
var probe = StubProbe.with_available([])
val rows = doctor_rows(empty_registry(), probe, "")
val details = doctor_detail_lines(rows)
assert_true(details.contains("metal profile: skip:metal-unavailable-not-macos"))
assert_true(details.contains("cuda profile:"))
```

</details>

### debug-doctor — live host probe (host-aware)

#### gives every row either ok or a stated skip reason, never a blank

- gives every row either ok or a stated skip reason, never a blank


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("gives every row either ok or a stated skip reason, never a blank")
var probe = LiveGpuBackendProbe.create()
val rows = doctor_rows(empty_registry(), probe, "")
for row in rows:
    val cell = row_attach_cell(row)
    assert_false(cell == "")
    if not row_is_attachable(row):
        # A non-attachable target must always say WHY.
        assert_true(row.attach.starts_with("skip:") or row.attach.starts_with("blocked:"))
        assert_true(row.attach.len() > 6)
```

</details>

#### skips metal cleanly on a non-macOS host, for metal's own reason

- skips metal cleanly on a non-macOS host, for metal's own reason
   - Expected: cap_level_name(row.debug_level) equals `unavailable`
   - Expected: row.profile.detail equals `row.attach`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("skips metal cleanly on a non-macOS host, for metal's own reason")
var probe = LiveGpuBackendProbe.create()
val row = gpu_row(empty_registry(), "metal", probe)
if row_is_attachable(row):
    # A real Metal host (a Mac): the skip contract does not apply.
    assert_true(true)
else:
    # Linux/Windows: rt_metal_is_available() hard-returns false, and
    # this is the CORRECT result -- asserted as such.
    assert_true(row.attach.starts_with("skip:metal-"))
    expect(cap_level_name(row.debug_level)).to_equal("unavailable")
    expect(row.profile.detail).to_equal(row.attach)
```

</details>

#### reports host and ref as attachable on any host

- reports host and ref as attachable on any host


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports host and ref as attachable on any host")
var probe = LiveGpuBackendProbe.create()
val rows = doctor_rows(empty_registry(), probe, "")
assert_true(row_is_attachable(rows[0]))
assert_true(row_is_attachable(rows[1]))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `720cf404cf6ef86ebe75b918cbfe78feccc360ec670b026ea9669e94f336250d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `720cf404cf6ef86ebe75b918cbfe78feccc360ec670b026ea9669e94f336250d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `720cf404cf6ef86ebe75b918cbfe78feccc360ec670b026ea9669e94f336250d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.spl
mirror: doc/06_spec/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'attaches the ref lane and acquires the group through one accessor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the debug level the ref target itself answers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug_doctor/debug_doctor_matrix_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports an EXACT emulated step count from a real run' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

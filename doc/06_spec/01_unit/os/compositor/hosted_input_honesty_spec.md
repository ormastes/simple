# Hosted Input Honesty Spec (Lane A4, cluster 4: sites 21-25)

> Verifies the hosted input honesty behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted Input Honesty Spec (Lane A4, cluster 4: sites 21-25)

Verifies the hosted input honesty behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | Done |
| Source | `test/01_unit/os/compositor/hosted_input_honesty_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the hosted input honesty behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### hosted_input_backend.spl — site 21, real mouse deltas

#### reports a nonzero, honest delta across two sequential positions

- Verify: reports a nonzero, honest delta across two sequential positions
   - Expected: first.dx equals `10)  # oracle: pinned constant asserted by this scenario`
   - Expected: first.dy equals `20)  # oracle: pinned constant asserted by this scenario`
   - Expected: second.dx equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: second.dy equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: reports a nonzero, honest delta across two sequential positions")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var backend = HostedInputBackend.create(0)
val first = backend.record_mouse_position(10, 20)
# From the (0,0) construction baseline, the first observed position
# IS the delta.
expect(first.dx).to_equal(10)  # oracle: pinned constant asserted by this scenario
expect(first.dy).to_equal(20)  # oracle: pinned constant asserted by this scenario

val second = backend.record_mouse_position(13, 25)
expect(second.dx).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(second.dy).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

#### reports an honest zero delta when position genuinely does not change

- Verify: reports an honest zero delta when position genuinely does not change
   - Expected: unchanged.dx equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: unchanged.dy equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: reports an honest zero delta when position genuinely does not change")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var backend = HostedInputBackend.create(0)
backend.record_mouse_position(50, 60)
val unchanged = backend.record_mouse_position(50, 60)
expect(unchanged.dx).to_equal(0)  # oracle: pinned constant asserted by this scenario
expect(unchanged.dy).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### hosted_input_backend.spl — site 22, mouse-button ABI matches the runtime's i64 shape

#### declares rt_winit_event_mouse_button as a plain i64 return, not a fabricated tuple

- Verify: declares rt_winit_event_mouse_button as a plain i64 return, not a fabricated tuple


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: declares rt_winit_event_mouse_button as a plain i64 return, not a fabricated tuple")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val source = hosted_input_backend_source()
expect(source).to_contain("extern fn rt_winit_event_mouse_button(ev: i64) -> i64")
expect(source).to_not_contain("rt_winit_event_mouse_button(ev: i64) -> (i64, bool)")
```

</details>

#### decodes pressed-ness through the real separate rt_winit_event_mouse_pressed accessor

- Verify: decodes pressed-ness through the real separate rt_winit_event_mouse_pressed accessor


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: decodes pressed-ness through the real separate rt_winit_event_mouse_pressed accessor")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val source = hosted_input_backend_source()
expect(source).to_contain("extern fn rt_winit_event_mouse_pressed(ev: i64) -> i64")
expect(source).to_contain("rt_winit_event_mouse_pressed(ev) != 0")
```

</details>

### hosted_input_sdl2.spl — sites 23/24, dead file deleted

#### no longer exists and has no remaining reference anywhere in src/ or test/

- Verify: no longer exists and has no remaining reference anywhere in src/ or test/
   - Expected: exists.trim() equals `GONE`
   - Expected: refs.trim() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: no longer exists and has no remaining reference anywhere in src/ or test/")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val exists = shell_output(
    'test -f src/os/compositor/hosted_input_sdl2.spl && echo EXISTS || echo GONE'
)
expect(exists.trim()).to_equal("GONE")

# Scoped to real code usage (an import or the class name), not
# prose: two files legitimately mention the filename in a comment
# (hosted_backend_sdl2.spl's docstring, sdl2_seam_subset_spec.spl's
# own note anticipating this deletion) and Rust build artifacts
# under target/ transiently embed every spec path as generated
# test-registration source -- none of those are a live reference.
val refs = shell_output(
    '/usr/bin/grep -rl -E "use os\\.compositor\\.hosted_input_sdl2\\b|\\bHostedSdl2Input\\b" src/ test/ 2>/dev/null | /usr/bin/grep -v "/target/" | sort -u'
)
expect(refs.trim()).to_equal("")
```

</details>

### arm64_virtio_input_backend.spl — site 25, unavailable reported honestly, not idle

#### create() reports unavailable because every rt_arm64_virtio_input_* extern is dangling

- Verify: create() reports unavailable because every rt_arm64_virtio_input_* extern is dangling
   - Expected: backend.poll_key() equals `nil`
   - Expected: backend.poll_mouse() equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: create() reports unavailable because every rt_arm64_virtio_input_* extern is dangling")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val backend = Arm64VirtioInputBackend.create(640, 480)
assert_false(backend.available())
# Unavailable must mean "never even attempts to pump", not merely
# "attempted and found nothing" -- both read as nil through the
# Option-shaped trait methods, but the flag is the honest signal.
expect(backend.poll_key()).to_equal(nil)
expect(backend.poll_mouse()).to_equal(nil)
```

</details>

#### create_with_poller's explicit available flag can honestly report true for a real injected backend

- Verify: create_with_poller's explicit available flag can honestly report true for a real injected backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: create_with_poller's explicit available flag can honestly report true for a real injected backend")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val backend = Arm64VirtioInputBackend.create_with_poller(
    640,
    480,
    fn() -> VirtioInputEvent?: nil,
    true
)
assert_true(backend.available())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dcdbbfdde72bb0680dcc600ad9fbfaa8581cc5e6763795f6288f56c1c09bf7ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dcdbbfdde72bb0680dcc600ad9fbfaa8581cc5e6763795f6288f56c1c09bf7ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dcdbbfdde72bb0680dcc600ad9fbfaa8581cc5e6763795f6288f56c1c09bf7ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/compositor/hosted_input_honesty_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/hosted_input_honesty_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/hosted_input_honesty_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/compositor/hosted_input_honesty_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/hosted_input_honesty_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

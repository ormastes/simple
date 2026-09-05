# web_engine2d_lane_matrix_parity_spec

> source == "cache"

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_engine2d_lane_matrix_parity_spec

source == "cache"

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

source == "cache"

fn _source_is_no_frame(source: text) -> bool:
    """The seven readback sources that produced no frame at all.

    Every one carries an EMPTY pixel array, so no frame-content assertion may
    run against them.

## Scenarios

### Web-render parity matrix across all four execution lanes

#### the reference frame itself (anti-vacuity)

#### the oracle is a real multi-colour scene, not a flat fill

- the oracle is a real multi-colour scene, not a flat fill
   - Expected: oracle.len() equals `SPEC_W * SPEC_H`
   - Expected: oracle[15 * SPEC_W + 5] equals `0xFF533483u32`
   - Expected: oracle[15 * SPEC_W + 51] equals `0xFF533483u32`
   - Expected: oracle[31 * SPEC_W + 5] equals `0xFF533483u32`
   - Expected: oracle[16 * SPEC_W + 6] equals `0xFF0F3460u32`
   - Expected: oracle[30 * SPEC_W + 63] equals `0xFF533483u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("the oracle is a real multi-colour scene, not a flat fill")
# THIS EXAMPLE IS THE MATRIX'S ANTI-VACUITY GUARD.
# Arrays are VALUE types in this language. If `_put`'s `mut`
# parameter failed to write back, `_reference_frame()` would return
# a uniform page-background fill -- and every lane would then agree
# on it bit-exactly, so all four parity comparisons would PASS while
# proving nothing at all. That is precisely the vacuous green this
# matrix exists to prevent, so the scene's structure is asserted
# before any lane is allowed to compare against it.
val oracle = _reference_frame()
expect(oracle.len()).to_equal(SPEC_W * SPEC_H)
# Every declared colour must actually be present.
expect(_count_color(oracle, 0xFF1A1A2Eu32)).to_be_greater_than(0)
expect(_count_color(oracle, 0xFF16213Eu32)).to_be_greater_than(0)
expect(_count_color(oracle, 0xFFA0C4FFu32)).to_be_greater_than(0)
expect(_count_color(oracle, 0xFF0F3460u32)).to_be_greater_than(0)
expect(_count_color(oracle, 0xFF533483u32)).to_be_greater_than(0)
expect(_count_color(oracle, 0xFFE0E0FFu32)).to_be_greater_than(0)
# A flat fill would have every pixel the same colour; require that
# the background is a MINORITY of the frame's distinct structure.
expect(_count_color(oracle, 0xFF1A1A2Eu32)).to_not_equal(SPEC_W * SPEC_H)
# The 1px border must be exactly where it was drawn -- this is what
# catches a write-back that silently lost the thin edges.
expect(oracle[15 * SPEC_W + 5]).to_equal(0xFF533483u32)
expect(oracle[15 * SPEC_W + 51]).to_equal(0xFF533483u32)
expect(oracle[31 * SPEC_W + 5]).to_equal(0xFF533483u32)
# ...and the card interior just inside that border must NOT be the
# border colour, so a fill that overran the edges also fails here.
expect(oracle[16 * SPEC_W + 6]).to_equal(0xFF0F3460u32)
# The odd-column vertical rule.
expect(oracle[30 * SPEC_W + 63]).to_equal(0xFF533483u32)
print "[lane-matrix] ORACLE VERIFIED: nonzero={_nonzero(oracle)} rowpair={_row_pair_identity(oracle)} bg={_count_color(oracle, 0xFF1A1A2Eu32)} of {SPEC_W * SPEC_H} -- multi-colour scene with intact 1px borders"
```

</details>

#### lane availability (skipped-and-why, never silently passed)

#### reports the SIMD gate honestly rather than inferring it

- reports the SIMD gate honestly rather than inferring it
   - Expected: simd_ok is true
   - Expected: simd_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports the SIMD gate honestly rather than inferring it")
# `cpu_simd` is the ONLY genuine SIMD lane. Its create is gated on
# native_pixel_rows_enabled(); when that is false the create must
# FAIL rather than quietly serve scalar pixels under the SIMD name.
val simd_ok = native_pixel_rows_enabled()
print "[lane-matrix] AVAILABILITY cpu_simd: native_pixel_rows_enabled={simd_ok}"
match Engine2D.create_requested_backend(SPEC_W, SPEC_H, "cpu_simd"):
    Ok(e):
        e.shutdown()
        # A create that succeeded proves the gate was open.
        if not simd_ok:
            print "[lane-matrix] AVAILABILITY cpu_simd: CREATE SUCCEEDED WITH THE GATE CLOSED -- scalar pixels would be served under the SIMD name; failing closed"
        expect(simd_ok).to_equal(true)
    Err(msg):
        print "[lane-matrix] AVAILABILITY cpu_simd: UNAVAILABLE reason='{msg}'"
        # Fail-closed is only correct if the gate really is closed.
        if simd_ok:
            print "[lane-matrix] AVAILABILITY cpu_simd: GATE OPEN BUT CREATE FAILED -- the SIMD lane is being reported unavailable on a SIMD-capable host"
        expect(simd_ok).to_equal(false)
```

</details>

#### reports metal as unavailable on this host rather than faking it

- reports metal as unavailable on this host rather than faking it


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports metal as unavailable on this host rather than faking it")
# Metal is an Apple API. On Linux the create must fail; a matrix
# that reported a metal pass here would be fabricating a lane.
match Engine2D.create_requested_backend(SPEC_W, SPEC_H, "metal"):
    Ok(e):
        e.shutdown()
        print "[lane-matrix] AVAILABILITY metal: create SUCCEEDED -- this is an Apple host"
    Err(msg):
        print "[lane-matrix] AVAILABILITY metal: UNAVAILABLE reason='{msg}' -- Metal is an Apple API and this is not an Apple host; the Vulkan/Metal matrix slot is served by vulkan"
        expect(msg).to_not_equal("")
```

</details>

#### reports opencl as unavailable rather than substituting another backend

- reports opencl as unavailable rather than substituting another backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports opencl as unavailable rather than substituting another backend")
match Engine2D.create_requested_backend(SPEC_W, SPEC_H, "opencl"):
    Ok(e):
        e.shutdown()
        print "[lane-matrix] AVAILABILITY opencl: create SUCCEEDED"
    Err(msg):
        print "[lane-matrix] AVAILABILITY opencl: UNAVAILABLE reason='{msg}'"
        expect(msg).to_not_equal("")
```

</details>

#### records that webgpu presents in software by construction

- records that webgpu presents in software by construction
   - Expected: _device_proven(res.source, res.handle, res.identity, res.pixel_count) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("records that webgpu presents in software by construction")
# backend_webgpu.spl:561 returns cpu_mirror unconditionally with
# emu_draw_* primitives. It is software BY CONSTRUCTION, so a
# device-provenance expectation there is a guaranteed false red.
# It is recorded as a software lane, not asserted as a GPU lane.
val oracle = _reference_frame()
val res = _render_lane("webgpu", oracle)
if not res.created:
    print "[lane-matrix] AVAILABILITY webgpu: UNAVAILABLE reason='{res.fail_reason}'"
else:
    print "[lane-matrix] AVAILABILITY webgpu: constructs, source={res.source} -- software by construction (backend_webgpu.spl:561 returns cpu_mirror unconditionally); NOT counted as a GPU lane"
    _assert_provenance_invariants("webgpu", res.source, res.handle, res.identity, res.pixel_count)
    # The load-bearing assertion: a software-by-construction lane
    # must never carry device credentials.
    expect(_device_proven(res.source, res.handle, res.identity, res.pixel_count)).to_equal(false)
```

</details>

#### lane 1 of 4 -- cpu (scalar reference)

#### cpu lane replays the oracle bit-exactly with honest cpu provenance

- cpu lane replays the oracle bit-exactly with honest cpu provenance
   - Expected: _source_is_device(res.source) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cpu lane replays the oracle bit-exactly with honest cpu provenance")
val oracle = _reference_frame()
expect(_nonzero(oracle)).to_be_greater_than(0)
val res = _render_lane("cpu", oracle)
if res.created:
    _assert_provenance_invariants("cpu", res.source, res.handle, res.identity, res.pixel_count)
    _report_outcome("cpu", res.source, res.handle, res.identity, res.pixel_count)
    # The scalar CPU lane must say it is CPU. A cpu create that came
    # back device-sourced would be a provenance defect.
    expect(_source_is_device(res.source)).to_equal(false)
_compare_lane("cpu", oracle, res)
```

</details>

#### lane 2 of 4 -- cpu_simd (SIMD pixel rows)

#### simd lane replays the oracle bit-exactly with honest cpu provenance

- simd lane replays the oracle bit-exactly with honest cpu provenance
   - Expected: _source_is_device(res.source) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("simd lane replays the oracle bit-exactly with honest cpu provenance")
val oracle = _reference_frame()
val res = _render_lane("cpu_simd", oracle)
if res.created:
    _assert_provenance_invariants("cpu_simd", res.source, res.handle, res.identity, res.pixel_count)
    _report_outcome("cpu_simd", res.source, res.handle, res.identity, res.pixel_count)
    expect(_source_is_device(res.source)).to_equal(false)
_compare_lane("cpu_simd", oracle, res)
```

</details>

#### lane 3 of 4 -- vulkan (portable GPU API; Metal slot on Apple)

#### vulkan lane replays the oracle bit-exactly and proves a device

- vulkan lane replays the oracle bit-exactly and proves a device


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("vulkan lane replays the oracle bit-exactly and proves a device")
val oracle = _reference_frame()
val res = _render_lane("vulkan", oracle)
if not res.created:
    # A create failure here is a device-availability event (the
    # per-process vulkan leak surfaces exactly this way), not a
    # defect in the code under test. Say so and assert nothing
    # about a device that is not present.
    print "[lane-matrix] vulkan: GPU BRANCH SKIPPED -- create failed at use time (reason='{res.fail_reason}'); this example proves NOTHING about the vulkan lane"
else:
    _assert_provenance_invariants("vulkan", res.source, res.handle, res.identity, res.pixel_count)
    val proven = _report_outcome("vulkan", res.source, res.handle, res.identity, res.pixel_count)
    print "[lane-matrix] vulkan: presented-arm source={res.presented_source} (present() clears `dirty`, so the presented read takes the host-cache arm by construction)"
    if not proven:
        # Not strictly proven. It must then be either honestly
        # device-attributed with real credentials, or an honest
        # cpu_fallback. A vulkan create that SUCCEEDED and returned
        # "cpu_mirror" means the GPU lane was silently reclassified
        # as CPU with no fallback recorded -- a bookkeeping defect,
        # not a device event, and it fails here.
        if res.source == "cpu_mirror":
            print "[lane-matrix] vulkan: SILENT CPU RECLASSIFICATION -- a live vulkan backend must report 'cpu_fallback' with a reason, never 'cpu_mirror'; failing closed"
        expect(res.source).to_not_equal("cpu_mirror")
        if _source_is_device(res.source):
            expect(res.handle).to_be_greater_than(0)
            expect(res.identity).to_be_greater_than(0)
_compare_lane("vulkan", oracle, res)
```

</details>

#### lane 4 of 4 -- cuda (direct CUDA)

#### cuda lane replays the oracle bit-exactly and proves a device

- cuda lane replays the oracle bit-exactly and proves a device


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cuda lane replays the oracle bit-exactly and proves a device")
# NOTE ON THE PROBE: probe_cuda() reports "CUDA runtime unavailable"
# from a cold process on this host while
# create_with_backend_strict("cuda") succeeds with real device
# readback. That divergence is permanent, not load-dependent
# (verified byte-identical with the kill-guard off), so the probe is
# NOT authoritative for cuda and this lane never consults it -- it
# creates and asserts on what the create returned.
val oracle = _reference_frame()
val res = _render_lane("cuda", oracle)
if not res.created:
    print "[lane-matrix] cuda: GPU BRANCH SKIPPED -- create failed at use time (reason='{res.fail_reason}'); this example proves NOTHING about the cuda lane"
else:
    _assert_provenance_invariants("cuda", res.source, res.handle, res.identity, res.pixel_count)
    val proven = _report_outcome("cuda", res.source, res.handle, res.identity, res.pixel_count)
    if not proven:
        if res.source == "cpu_mirror":
            print "[lane-matrix] cuda: SILENT CPU RECLASSIFICATION -- a live cuda backend must report 'cpu_fallback' with a reason, never 'cpu_mirror'; failing closed"
        expect(res.source).to_not_equal("cpu_mirror")
_compare_lane("cuda", oracle, res)
```

</details>

#### cross-lane divergence

#### characterises any disagreement between the four lanes

- characterises any disagreement between the four lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("characterises any disagreement between the four lanes")
# All four lanes replay the SAME single pixel source, so any
# pairwise disagreement is a rasterizer difference and is reported
# as a FINDING -- decomposed into oracle-only / lane-only /
# differing with the adjacent-row-pair signature -- never resolved
# by picking a winner or loosening the bound.
val oracle = _reference_frame()
print "[lane-matrix] ORACLE: nonzero={_nonzero(oracle)} rowpair={_row_pair_identity(oracle)}"
val cpu = _render_lane("cpu", oracle)
val simd = _render_lane("cpu_simd", oracle)
val vk = _render_lane("vulkan", oracle)
val cu = _render_lane("cuda", oracle)
var compared = 0
if cpu.created and simd.created:
    val d = _diffcount(cpu.px, simd.px)
    print "[lane-matrix] COMPARED divergence/cpu-vs-simd: diff={d} cpu_rowpair={_row_pair_identity(cpu.px)} simd_rowpair={_row_pair_identity(simd.px)}"
    if d != 0:
        _decompose("cpu-vs-simd", cpu.px, simd.px)
    compared = compared + 1
else:
    print "[lane-matrix] SKIP divergence/cpu-vs-simd: a lane was unavailable -- NOT COMPARED"
if cpu.created and vk.created:
    val d = _diffcount(cpu.px, vk.px)
    print "[lane-matrix] COMPARED divergence/cpu-vs-vulkan: diff={d} cpu_rowpair={_row_pair_identity(cpu.px)} vulkan_rowpair={_row_pair_identity(vk.px)}"
    if d != 0:
        _decompose("cpu-vs-vulkan", cpu.px, vk.px)
    compared = compared + 1
else:
    print "[lane-matrix] SKIP divergence/cpu-vs-vulkan: a lane was unavailable -- NOT COMPARED"
if cpu.created and cu.created:
    val d = _diffcount(cpu.px, cu.px)
    print "[lane-matrix] COMPARED divergence/cpu-vs-cuda: diff={d} cpu_rowpair={_row_pair_identity(cpu.px)} cuda_rowpair={_row_pair_identity(cu.px)}"
    if d != 0:
        _decompose("cpu-vs-cuda", cpu.px, cu.px)
    compared = compared + 1
else:
    print "[lane-matrix] SKIP divergence/cpu-vs-cuda: a lane was unavailable -- NOT COMPARED"
if vk.created and cu.created:
    val d = _diffcount(vk.px, cu.px)
    print "[lane-matrix] COMPARED divergence/vulkan-vs-cuda: diff={d} vulkan_rowpair={_row_pair_identity(vk.px)} cuda_rowpair={_row_pair_identity(cu.px)}"
    if d != 0:
        _decompose("vulkan-vs-cuda", vk.px, cu.px)
    compared = compared + 1
else:
    print "[lane-matrix] SKIP divergence/vulkan-vs-cuda: a lane was unavailable -- NOT COMPARED"
print "[lane-matrix] DIVERGENCE VERDICT: {compared} of 4 pairwise lane comparisons ran in this example."
```

</details>

#### the real web-render oracle across the lanes

#### replays an actual web render through every available lane

- replays an actual web render through every available lane
   - Expected: oracle.len() equals `SPEC_W * SPEC_H`


<details>
<summary>Executable SSpec</summary>

Runnable source: 44 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("replays an actual web render through every available lane")
# The four comparisons above deliberately use the DETERMINISTIC
# reference frame, because the web layout renderer's output is
# wall-clock-budget degradable and a degradable oracle is a
# confound on a matrix whose whole purpose is to isolate the
# BACKEND axis: two lanes could be compared against two different
# oracles and the disagreement would be blamed on a backend.
#
# This example closes the remaining gap -- it drives the SAME
# replay with a genuine web render, so the matrix is demonstrably
# wired to the web renderer and not only to a synthetic scene.
val html = "<html><head><style>" +
    "body { background-color: #1a1a2e; }" +
    ".card { background-color: #0f3460; border: 2px solid #533483; }" +
    "</style></head><body>" +
    "<div class='card'><p>lane matrix</p></div>" +
    "</body></html>"
val oracle = simple_web_layout_render_html_pixels(html, SPEC_W, SPEC_H, "cpu")
val degraded = simple_web_layout_last_render_degraded()
if degraded:
    val reason = simple_web_layout_last_render_degrade_reason()
    # Every budget exhaustion must NAME its exit site. An anonymous
    # degrade is a provenance-bookkeeping defect, not a host event
    # -- and the four style-cascade guards were unreachable at this
    # base precisely because they called a function that did not
    # exist, so this assertion is load-bearing here.
    print "[lane-matrix] WEB ORACLE: degraded at site '{reason}'"
    expect(reason).to_not_equal("")
expect(oracle.len()).to_equal(SPEC_W * SPEC_H)
print "[lane-matrix] WEB ORACLE: nonzero={_nonzero(oracle)} rowpair={_row_pair_identity(oracle)} degraded={degraded}"
if _nonzero(oracle) == 0:
    print "[lane-matrix] SKIP web-oracle: the web render produced an empty frame -- NOT COMPARED; this example proves NOTHING about web-render lane parity"
else:
    val vk = _render_lane("vulkan", oracle)
    val cu = _render_lane("cuda", oracle)
    if vk.created:
        _assert_provenance_invariants("web-oracle/vulkan", vk.source, vk.handle, vk.identity, vk.pixel_count)
        _report_outcome("web-oracle/vulkan", vk.source, vk.handle, vk.identity, vk.pixel_count)
    _compare_lane("web-oracle/vulkan", oracle, vk)
    if cu.created:
        _assert_provenance_invariants("web-oracle/cuda", cu.source, cu.handle, cu.identity, cu.pixel_count)
        _report_outcome("web-oracle/cuda", cu.source, cu.handle, cu.identity, cu.pixel_count)
    _compare_lane("web-oracle/cuda", oracle, cu)
```

</details>

#### run verdict

#### states the denominator so a pass cannot be misread as complete

- states the denominator so a pass cannot be misread as complete
   - Expected: PARITY_COMPARISONS_DECLARED equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("states the denominator so a pass cannot be misread as complete")
print "[lane-matrix] RUN VERDICT: this run DECLARES {PARITY_COMPARISONS_DECLARED} lane-vs-oracle parity comparisons (cpu, cpu_simd, vulkan, cuda)."
print "[lane-matrix] RUN VERDICT: the number that ACTUALLY RAN is `grep -c '^.lane-matrix. COMPARED '`; the number skipped is `grep -c '^.lane-matrix. SKIP '`. Anchor at line start -- these verdict lines mention the tokens too, and an unanchored count reads the verdict's own prose as evidence."
print "[lane-matrix] RUN VERDICT: this run's GPU evidence is exactly the set of '[lane-matrix] <lane>: GPU-PROVEN' lines. Every 'GPU BRANCH SKIPPED' line marks an example that proves NOTHING about the GPU path."
# The GPU-PROVEN receipts carry a VARIABLE label between the tag and
# the token, so no fixed prefix anchors them the way `^... COMPARED `
# anchors the parity receipts. A bare `grep -c GPU-PROVEN` therefore
# counts THIS verdict line too and over-reports by one -- measured:
# 5 against 4 real receipts. State the subtraction explicitly rather
# than leave a counting rule that silently inflates.
print "[lane-matrix] RUN VERDICT: count GPU-PROVEN with `grep -a 'GPU-PROVEN' | grep -av 'RUN VERDICT' | wc -l`. A bare `grep -c 'GPU-PROVEN'` counts this verdict line as evidence and over-reports by exactly one."
print "[lane-matrix] RUN VERDICT: a PASS with fewer than {PARITY_COMPARISONS_DECLARED} lane-vs-oracle COMPARED receipts is INCONCLUSIVE, not a parity pass -- a lane was unavailable and its comparison was never made."
print "[lane-matrix] RUN VERDICT: cpu and cpu_simd are CPU lanes by design; a run whose only COMPARED receipts are cpu/cpu_simd proves NOTHING about GPU offload, regardless of the example count."
expect(PARITY_COMPARISONS_DECLARED).to_equal(4)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `65be93bca9b07c0b3326b16ce7f40e30a6e2e289dae3759e5143a2426e95b262`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65be93bca9b07c0b3326b16ce7f40e30a6e2e289dae3759e5143a2426e95b262`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65be93bca9b07c0b3326b16ce7f40e30a6e2e289dae3759e5143a2426e95b262`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.spl
mirror: doc/06_spec/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.spl:435:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the oracle is a real multi-colour scene, not a flat fill' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.spl:472:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the SIMD gate honestly rather than inferring it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/rendering/web_engine2d_lane_matrix_parity_spec.spl:494:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports metal as unavailable on this host rather than faking it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

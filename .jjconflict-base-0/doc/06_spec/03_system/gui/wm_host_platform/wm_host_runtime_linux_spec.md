# WM/GUI Host Seam — Linux Runtime Conformance

> The RUNTIME-NATIVE tier of this suite. Everything here actually EXECUTES the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM/GUI Host Seam — Linux Runtime Conformance

The RUNTIME-NATIVE tier of this suite. Everything here actually EXECUTES the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | In Progress |
| Source | `test/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The RUNTIME-NATIVE tier of this suite. Everything here actually EXECUTES the
2D-surface seam and the event-decode seam in-process on the host running the
spec, and asserts observable state changes rather than return codes.

## Scope and Preconditions

Guarded by `host_os()`. On a non-Linux host every example short-circuits and
makes no claim; the evidence-tier ledger
(`wm_host_evidence_tier_spec.spl`) is what records why.

## Compatibility and Limitations

HONEST STATEMENT OF WHAT THIS DOES AND DOES NOT PROVE.

`DISPLAY` and `WAYLAND_DISPLAY` are unset in this environment, and the winit
path's buffer handles come from an interpreter-only extern family. So this
file exercises the HEADLESS seam implementation
(`HeadlessHostCompositorBackend`), which is the implementation every live
path currently falls through to.

It therefore proves: the seam's surface semantics are real — a surface handle
is usable, drawing mutates the pixels that are read back, and presentation is
observable and strictly advances.

It does NOT prove that a pixel reached a physical screen or a display server.
No such claim is made anywhere in this suite, on any platform.

Assertions deliberately require STRICT advancement (`t1 > t0`), never
`t1 >= t0`: a counter or clock frozen at zero satisfies `0 >= 0` and would
make a dead implementation look alive.

## Scenarios

### WM host seam runtime (linux) — surface creation

#### surface creation returns a usable handle with the requested geometry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- surface creation returns a usable handle with the requested geometry
   - Expected: b.width() equals `32`
   - Expected: b.height() equals `16`
   - Expected: headless_host_compositor_pixels(b).len() equals `32 * 16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("surface creation returns a usable handle with the requested geometry")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(32, 16)
    expect(b.width()).to_equal(32)
    expect(b.height()).to_equal(16)
    # A usable handle must expose a real backing store, not an empty
    # placeholder that later silently discards every draw.
    expect(headless_host_compositor_pixels(b).len()).to_equal(32 * 16)
```

</details>

#### rejects a degenerate surface instead of returning a fake one

- rejects a degenerate surface instead of returning a fake one
   - Expected: headless_host_compositor_pixels(b).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects a degenerate surface instead of returning a fake one")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(0, 0)
    expect(headless_host_compositor_pixels(b).len()).to_equal(0)
```

</details>

### WM host seam runtime (linux) — drawing mutates the surface

#### clear writes the requested colour into every pixel

- clear writes the requested colour into every pixel
   - Expected: after[0] equals `0x00FF0000u32`
   - Expected: after[15] equals `0x00FF0000u32`
   - Expected: after[0] != before is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clear writes the requested colour into every pixel")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(4, 4)
    val before = headless_host_compositor_pixels(b)[0]
    b.clear(0x00FF0000u32)
    val after = headless_host_compositor_pixels(b)
    # Value equality, not "the call returned true".
    expect(after[0]).to_equal(0x00FF0000u32)
    expect(after[15]).to_equal(0x00FF0000u32)
    expect(after[0] != before).to_equal(true)
```

</details>

#### put_pixel affects the addressed pixel and leaves its neighbour alone

- put_pixel affects the addressed pixel and leaves its neighbour alone
   - Expected: px[1 * 4 + 2] equals `0x0000FF00u32`
   - Expected: px[1 * 4 + 3] equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("put_pixel affects the addressed pixel and leaves its neighbour alone")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(4, 4)
    b.clear(0x00000000u32)
    b.put_pixel(2, 1, 0x0000FF00u32)
    val px = headless_host_compositor_pixels(b)
    # Index arithmetic proves the write landed at the right address,
    # which a blanket "fill everything" stub would fail.
    expect(px[1 * 4 + 2]).to_equal(0x0000FF00u32)
    expect(px[1 * 4 + 3]).to_equal(0x00000000u32)
```

</details>

#### fill_rect covers exactly the requested region

- fill_rect covers exactly the requested region
   - Expected: px[2 * 8 + 2] equals `0x000000FFu32`
   - Expected: px[4 * 8 + 4] equals `0x000000FFu32`
   - Expected: px[1 * 8 + 2] equals `0x00000000u32`
   - Expected: px[5 * 8 + 5] equals `0x00000000u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fill_rect covers exactly the requested region")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(8, 8)
    b.clear(0x00000000u32)
    b.fill_rect(2, 2, 3, 3, 0x000000FFu32)
    val px = headless_host_compositor_pixels(b)
    expect(px[2 * 8 + 2]).to_equal(0x000000FFu32)
    expect(px[4 * 8 + 4]).to_equal(0x000000FFu32)
    # Just outside the rect must be untouched.
    expect(px[1 * 8 + 2]).to_equal(0x00000000u32)
    expect(px[5 * 8 + 5]).to_equal(0x00000000u32)
```

</details>

#### blit_pixels transfers caller pixels into the surface

- blit_pixels transfers caller pixels into the surface
   - Expected: px[0] equals `0x00ABCDEFu32`
   - Expected: px[1] equals `0x00ABCDEFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blit_pixels transfers caller pixels into the surface")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(4, 4)
    b.clear(0x00000000u32)
    val src = [0x00ABCDEFu32, 0x00ABCDEFu32, 0x00ABCDEFu32, 0x00ABCDEFu32]
    b.blit_pixels(0, 0, 2, 2, src)
    val px = headless_host_compositor_pixels(b)
    expect(px[0]).to_equal(0x00ABCDEFu32)
    expect(px[1]).to_equal(0x00ABCDEFu32)
```

</details>

#### resize reallocates the backing store

- resize reallocates the backing store
   - Expected: headless_host_compositor_pixels(b).len() equals `16`
   - Expected: b.width() equals `6`
   - Expected: b.height() equals `5`
   - Expected: headless_host_compositor_pixels(b).len() equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("resize reallocates the backing store")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(4, 4)
    expect(headless_host_compositor_pixels(b).len()).to_equal(16)
    headless_host_compositor_resize(b, 6, 5)
    expect(b.width()).to_equal(6)
    expect(b.height()).to_equal(5)
    expect(headless_host_compositor_pixels(b).len()).to_equal(30)
```

</details>

### WM host seam runtime (linux) — presentation is observable

#### present strictly advances the presentation counter

- present strictly advances the presentation counter
   - Expected: t1 > t0 is true
   - Expected: b.present_count > t1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("present strictly advances the presentation counter")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(4, 4)
    val t0 = b.present_count
    b.present()
    val t1 = b.present_count
    # STRICT: a counter frozen at 0 passes `t1 >= t0` and would make
    # a dead present() look alive. It cannot pass `t1 > t0`.
    expect(t1 > t0).to_equal(true)
    b.present()
    expect(b.present_count > t1).to_equal(true)
```

</details>

#### present_rect is also observable

- present_rect is also observable
   - Expected: b.present_count > t0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("present_rect is also observable")
if runtime_tier_active():
    val b = HeadlessHostCompositorBackend.new(4, 4)
    val t0 = b.present_count
    b.present_rect(0, 0, 2, 2)
    expect(b.present_count > t0).to_equal(true)
```

</details>

### WM host seam runtime (linux) — event delivery

#### pointer button codes decode to distinct labels

- pointer button codes decode to distinct labels
   - Expected: wm_pointer_button_from_code(1) equals `left`
   - Expected: wm_pointer_button_from_code(2) equals `middle`
   - Expected: wm_pointer_button_from_code(3) equals `right`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pointer button codes decode to distinct labels")
if runtime_tier_active():
    expect(wm_pointer_button_from_code(1)).to_equal("left")
    expect(wm_pointer_button_from_code(2)).to_equal("middle")
    expect(wm_pointer_button_from_code(3)).to_equal("right")
```

</details>

#### an unknown pointer button decodes to none rather than a plausible lie

- an unknown pointer button decodes to none rather than a plausible lie
   - Expected: wm_pointer_button_from_code(0) equals `none`
   - Expected: wm_pointer_button_from_code(99) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("an unknown pointer button decodes to none rather than a plausible lie")
if runtime_tier_active():
    expect(wm_pointer_button_from_code(0)).to_equal("none")
    expect(wm_pointer_button_from_code(99)).to_equal("none")
```

</details>

#### pointer event kinds decode to distinct labels

- pointer event kinds decode to distinct labels
   - Expected: wm_pointer_kind_from_code(1) equals `down`
   - Expected: wm_pointer_kind_from_code(2) equals `up`
   - Expected: wm_pointer_kind_from_code(3) equals `move`
   - Expected: wm_pointer_kind_from_code(0) equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pointer event kinds decode to distinct labels")
if runtime_tier_active():
    expect(wm_pointer_kind_from_code(1)).to_equal("down")
    expect(wm_pointer_kind_from_code(2)).to_equal("up")
    expect(wm_pointer_kind_from_code(3)).to_equal("move")
    expect(wm_pointer_kind_from_code(0)).to_equal("none")
```

</details>

#### keyboard scancodes decode with shift state honoured

- keyboard scancodes decode with shift state honoured
   - Expected: ps2_wm_character(0x10, false) equals `q`
   - Expected: ps2_wm_character(0x10, true) equals `Q`
   - Expected: ps2_wm_character(0x02, false) equals `1`
   - Expected: ps2_wm_character(0x02, true) equals `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keyboard scancodes decode with shift state honoured")
if runtime_tier_active():
    expect(ps2_wm_character(0x10, false)).to_equal("q")
    expect(ps2_wm_character(0x10, true)).to_equal("Q")
    expect(ps2_wm_character(0x02, false)).to_equal("1")
    expect(ps2_wm_character(0x02, true)).to_equal("!")
```

</details>

#### decoded key names are non-empty for known scancodes

- decoded key names are non-empty for known scancodes
   - Expected: ps2_wm_key_name(0x10).len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decoded key names are non-empty for known scancodes")
if runtime_tier_active():
    expect(ps2_wm_key_name(0x10).len() > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-WM-HOST-PLATFORM-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9b39dafbaf58b2722b277623bd7029dc0c2ac2e74a2810fe1956381e4f9a334d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9b39dafbaf58b2722b277623bd7029dc0c2ac2e74a2810fe1956381e4f9a334d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9b39dafbaf58b2722b277623bd7029dc0c2ac2e74a2810fe1956381e4f9a334d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.spl
mirror: doc/06_spec/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'surface creation returns a usable handle with the requested geometry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a degenerate surface instead of returning a fake one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clear writes the requested colour into every pixel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

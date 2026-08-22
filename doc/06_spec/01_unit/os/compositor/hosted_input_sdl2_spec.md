# SDL2 Host Input Backend Spec

> Verifies the hosted input sdl2 behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SDL2 Host Input Backend Spec

Verifies the hosted input sdl2 behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | Done |
| Source | `test/01_unit/os/compositor/hosted_input_sdl2_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the hosted input sdl2 behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### sdl2 wheel sign
_The single sign negation on the SDL2 path, at the free function._

#### negates a scroll-up detent into positive-down

- Verify: negates a scroll-up detent into positive-down
   - Expected: sdl2_wheel_to_mouse_wheel(1) equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: negates a scroll-up detent into positive-down")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""SDL2 wheel_y +1 means scrolling UP; MouseEvent.wheel is
positive-DOWN, so it must come out as -1."""
expect(sdl2_wheel_to_mouse_wheel(1)).to_equal(0 - 1)
```

</details>

#### negates a scroll-down detent into negative

- Verify: negates a scroll-down detent into negative
   - Expected: sdl2_wheel_to_mouse_wheel(0 - 1) equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: negates a scroll-down detent into negative")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(sdl2_wheel_to_mouse_wheel(0 - 1)).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### leaves a zero detent alone

- Verify: leaves a zero detent alone
   - Expected: sdl2_wheel_to_mouse_wheel(0) equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: leaves a zero detent alone")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(sdl2_wheel_to_mouse_wheel(0)).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

#### flips a multi-detent burst without scaling it

- Verify: flips a multi-detent burst without scaling it
   - Expected: sdl2_wheel_to_mouse_wheel(3) equals `0 - 3`
   - Expected: sdl2_wheel_to_mouse_wheel(0 - 7) equals `7)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: flips a multi-detent burst without scaling it")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(sdl2_wheel_to_mouse_wheel(3)).to_equal(0 - 3)
expect(sdl2_wheel_to_mouse_wheel(0 - 7)).to_equal(7)  # oracle: pinned constant asserted by this scenario
```

</details>

#### flips exactly once, not twice

- Verify: flips exactly once, not twice
   - Expected: sdl2_wheel_to_mouse_wheel(5) equals `0 - 5`
   - Expected: sdl2_wheel_to_mouse_wheel(sdl2_wheel_to_mouse_wheel(5)) equals `5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: flips exactly once, not twice")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
"""A double negation would be the identity. Pin that it is NOT."""
expect(sdl2_wheel_to_mouse_wheel(5)).to_equal(0 - 5)
expect(sdl2_wheel_to_mouse_wheel(sdl2_wheel_to_mouse_wheel(5))).to_equal(5)  # oracle: pinned constant asserted by this scenario
```

</details>

### record_wheel end to end
_The same flip, observed through a built MouseEvent._

#### carries the single flip into the built MouseEvent

- Verify: carries the single flip into the built MouseEvent
   - Expected: ev.wheel equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: carries the single flip into the built MouseEvent")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
val ev = b.record_wheel(1)
expect(ev.wheel).to_equal(0 - 1)
```

</details>

#### carries a scroll-down detent as positive

- Verify: carries a scroll-down detent as positive
   - Expected: ev.wheel equals `2)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: carries a scroll-down detent as positive")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
val ev = b.record_wheel(0 - 2)
expect(ev.wheel).to_equal(2)  # oracle: pinned constant asserted by this scenario
```

</details>

#### clears the wheel after one event (one-shot detent)

- Verify: clears the wheel after one event (one-shot detent)
   - Expected: first.wheel equals `0 - 1`
   - Expected: second.wheel equals `0)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: clears the wheel after one event (one-shot detent)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
val first = b.record_wheel(1)
expect(first.wheel).to_equal(0 - 1)
val second = b.record_mouse_position(0, 0)
expect(second.wheel).to_equal(0)  # oracle: pinned constant asserted by this scenario
```

</details>

### availability honesty
_A backend with no live SDL2 window says so instead of polling into the void._

#### reports unavailable for a zero window handle

- Verify: reports unavailable for a zero window handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: reports unavailable for a zero window handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val b = Sdl2InputBackend.create(0)
assert_false(b.is_available())
```

</details>

#### explains why it is unavailable

- Verify: explains why it is unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: explains why it is unavailable")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val b = Sdl2InputBackend.create(0)
expect(b.unavailable_reason()).to_contain("sdl2 window handle is 0")
```

</details>

#### reports available for a live window handle

- Verify: reports available for a live window handle
   - Expected: b.unavailable_reason() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: reports available for a live window handle")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val b = Sdl2InputBackend.create(42)
assert_true(b.is_available())
expect(b.unavailable_reason()).to_equal("")
```

</details>

#### create_unavailable preserves the caller's reason

- Verify: create_unavailable preserves the caller's reason
   - Expected: b.unavailable_reason() equals `SDL2 not built in`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: create_unavailable preserves the caller's reason")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val b = Sdl2InputBackend.create_unavailable("SDL2 not built in")
assert_false(b.is_available())
expect(b.unavailable_reason()).to_equal("SDL2 not built in")
```

</details>

### apply_mouse_button edges
_Edge-triggered button state, driven without SDL2._

#### reports a left press as pressed and just-pressed once

- Verify: reports a left press as pressed and just-pressed once


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: reports a left press as pressed and just-pressed once")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
b.apply_mouse_button(0, true)
val ev = b.record_mouse_position(10, 20)
assert_true(ev.left_pressed)
assert_true(ev.left_just_pressed)
assert_false(ev.left_just_released)
```

</details>

#### does not repeat just-pressed while held

- Verify: does not repeat just-pressed while held


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: does not repeat just-pressed while held")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
b.apply_mouse_button(0, true)
b.record_mouse_position(10, 20)
b.apply_mouse_button(0, true)
val ev = b.record_mouse_position(11, 21)
assert_true(ev.left_pressed)
assert_false(ev.left_just_pressed)
```

</details>

#### reports a left release as just-released

- Verify: reports a left release as just-released


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: reports a left release as just-released")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
b.apply_mouse_button(0, true)
b.record_mouse_position(1, 1)
b.apply_mouse_button(0, false)
val ev = b.record_mouse_position(1, 1)
assert_false(ev.left_pressed)
assert_true(ev.left_just_released)
```

</details>

#### tracks right and middle buttons independently of left

- Verify: tracks right and middle buttons independently of left


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: tracks right and middle buttons independently of left")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
b.apply_mouse_button(1, true)
b.apply_mouse_button(2, true)
val ev = b.record_mouse_position(0, 0)
assert_false(ev.left_pressed)
assert_true(ev.right_pressed)
assert_true(ev.middle_pressed)
assert_true(ev.right_just_pressed)
```

</details>

#### marks mouse state as buffered

- Verify: marks mouse state as buffered


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: marks mouse state as buffered")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
assert_false(b.has_buffered_mouse())
b.apply_mouse_button(0, true)
assert_true(b.has_buffered_mouse())
```

</details>

### record_mouse_position deltas
_Movement deltas are real, not hardcoded zeros._

#### reports real movement deltas, not zeros

- Verify: reports real movement deltas, not zeros
   - Expected: ev.x equals `13)  # oracle: pinned constant asserted by this scenario`
   - Expected: ev.y equals `7)  # oracle: pinned constant asserted by this scenario`
   - Expected: ev.dx equals `3)  # oracle: pinned constant asserted by this scenario`
   - Expected: ev.dy equals `0 - 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: reports real movement deltas, not zeros")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
b.record_mouse_position(10, 10)
val ev = b.record_mouse_position(13, 7)
expect(ev.x).to_equal(13)  # oracle: pinned constant asserted by this scenario
expect(ev.y).to_equal(7)  # oracle: pinned constant asserted by this scenario
expect(ev.dx).to_equal(3)  # oracle: pinned constant asserted by this scenario
expect(ev.dy).to_equal(0 - 3)
```

</details>

### keysym translation
_SDL keysyms become distinct Key values, or nil when unmapped._

#### maps lowercase letters to distinct keys, not all to Key.A

- Verify: maps lowercase letters to distinct keys, not all to Key.A
   - Expected: b.key_to_char(ka) equals `a`
   - Expected: b.key_to_char(kz) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: maps lowercase letters to distinct keys, not all to Key.A")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
if val ka = sdl2_keysym_to_key(97):
    expect(b.key_to_char(ka)).to_equal("a")
else:
    assert_true(false)
if val kz = sdl2_keysym_to_key(122):
    expect(b.key_to_char(kz)).to_equal("z")
else:
    assert_true(false)
```

</details>

#### maps digits

- Verify: maps digits
   - Expected: b.key_to_char(k5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: maps digits")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
if val k5 = sdl2_keysym_to_key(53):
    expect(b.key_to_char(k5)).to_equal("5")
else:
    assert_true(false)
```

</details>

#### maps punctuation

- Verify: maps punctuation
   - Expected: b.key_to_char(kc) equals `,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: maps punctuation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
if val kc = sdl2_keysym_to_key(44):
    expect(b.key_to_char(kc)).to_equal(",")
else:
    assert_true(false)
```

</details>

#### returns nil for an unmapped keysym rather than guessing

- Verify: returns nil for an unmapped keysym rather than guessing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: returns nil for an unmapped keysym rather than guessing")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(sdl2_keysym_to_key(999999)).to_be_nil()
```

</details>

#### maps a scancode-derived navigation keysym

- Verify: maps a scancode-derived navigation keysym


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: maps a scancode-derived navigation keysym")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
if val kup = sdl2_keysym_to_key(1073741906):
    var b = offline_backend()
    expect(b.key_to_char(kup)).to_be_nil()
else:
    assert_true(false)
```

</details>

### key_to_char shift handling
_Character output tracks the SDL modifier bitfield._

#### yields lowercase with no modifiers

- Verify: yields lowercase with no modifiers
   - Expected: b.key_to_char(Key.A) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: yields lowercase with no modifiers")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
expect(b.key_to_char(Key.A)).to_equal("a")
```

</details>

#### yields uppercase once SDL reports a shift modifier

- Verify: yields uppercase once SDL reports a shift modifier
   - Expected: b.key_to_char(Key.A) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: yields uppercase once SDL reports a shift modifier")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
b.apply_key_mods(0x0003)
assert_true(b.shift_held())
expect(b.key_to_char(Key.A)).to_equal("A")
```

</details>

#### yields shifted punctuation

- Verify: yields shifted punctuation
   - Expected: b.key_to_char(Key.Num1) equals `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: yields shifted punctuation")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
b.apply_key_mods(0x0003)
expect(b.key_to_char(Key.Num1)).to_equal("!")
```

</details>

#### adopts ctrl and alt from the SDL modifier bitfield

- Verify: adopts ctrl and alt from the SDL modifier bitfield


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: adopts ctrl and alt from the SDL modifier bitfield")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
b.apply_key_mods(0x00C0)
assert_true(b.ctrl_held())
assert_false(b.alt_held())
b.apply_key_mods(0x0300)
assert_true(b.alt_held())
assert_false(b.ctrl_held())
```

</details>

#### returns nil for a key with no character

- Verify: returns nil for a key with no character


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-WM-HOST-PLATFORM-003
step("Verify: returns nil for a key with no character")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
var b = offline_backend()
expect(b.key_to_char(Key.F1)).to_be_nil()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f6c66d0905357bbb91fd530a4f6b30a2a39a86b676f021fa573bcdc692930882`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f6c66d0905357bbb91fd530a4f6b30a2a39a86b676f021fa573bcdc692930882`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f6c66d0905357bbb91fd530a4f6b30a2a39a86b676f021fa573bcdc692930882`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/compositor/hosted_input_sdl2_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/hosted_input_sdl2_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/compositor/hosted_input_sdl2_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/compositor/hosted_input_sdl2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/hosted_input_sdl2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

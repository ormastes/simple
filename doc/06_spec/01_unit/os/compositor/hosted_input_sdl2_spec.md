# SDL2 Host Input Backend Spec

> `src/os/compositor/hosted_input_sdl2.spl` had ZERO coverage, including

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SDL2 Host Input Backend Spec

`src/os/compositor/hosted_input_sdl2.spl` had ZERO coverage, including

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing |
| Status | Done |
| Source | `test/01_unit/os/compositor/hosted_input_sdl2_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`src/os/compositor/hosted_input_sdl2.spl` had ZERO coverage, including
`sdl2_wheel_to_mouse_wheel` — the ONLY sign negation in the whole input
system. PS/2 is positive-down on the wire and passes through unnegated; SDL2
is positive-up and must flip exactly once. A wrong or doubled flip inverts
scrolling everywhere and nothing else in the tree would notice.

This spec pins:

- the wheel sign, at the free function AND end-to-end through `record_wheel`
- `create` / `create_unavailable` availability honesty
- `apply_mouse_button` edge-triggered state
- the keysym -> `Key` translation seam and `key_to_char` shift handling

Every seam used here is hardware-free: the backend is constructed with window
handle 0, so no SDL2 extern is ever called.

## Scenarios

### sdl2 wheel sign

#### negates a scroll-up detent into positive-down

- negates a scroll-up detent into positive-down
   - Expected: sdl2_wheel_to_mouse_wheel(1) equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("negates a scroll-up detent into positive-down")
"""SDL2 wheel_y +1 means scrolling UP; MouseEvent.wheel is
positive-DOWN, so it must come out as -1."""
expect(sdl2_wheel_to_mouse_wheel(1)).to_equal(0 - 1)
```

</details>

#### negates a scroll-down detent into negative

- negates a scroll-down detent into negative
   - Expected: sdl2_wheel_to_mouse_wheel(0 - 1) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("negates a scroll-down detent into negative")
expect(sdl2_wheel_to_mouse_wheel(0 - 1)).to_equal(1)
```

</details>

#### leaves a zero detent alone

- leaves a zero detent alone
   - Expected: sdl2_wheel_to_mouse_wheel(0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("leaves a zero detent alone")
expect(sdl2_wheel_to_mouse_wheel(0)).to_equal(0)
```

</details>

#### flips a multi-detent burst without scaling it

- flips a multi-detent burst without scaling it
   - Expected: sdl2_wheel_to_mouse_wheel(3) equals `0 - 3`
   - Expected: sdl2_wheel_to_mouse_wheel(0 - 7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("flips a multi-detent burst without scaling it")
expect(sdl2_wheel_to_mouse_wheel(3)).to_equal(0 - 3)
expect(sdl2_wheel_to_mouse_wheel(0 - 7)).to_equal(7)
```

</details>

#### flips exactly once, not twice

- flips exactly once, not twice
   - Expected: sdl2_wheel_to_mouse_wheel(5) equals `0 - 5`
   - Expected: sdl2_wheel_to_mouse_wheel(sdl2_wheel_to_mouse_wheel(5)) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("flips exactly once, not twice")
"""A double negation would be the identity. Pin that it is NOT."""
expect(sdl2_wheel_to_mouse_wheel(5)).to_equal(0 - 5)
expect(sdl2_wheel_to_mouse_wheel(sdl2_wheel_to_mouse_wheel(5))).to_equal(5)
```

</details>

### record_wheel end to end
_The same flip, observed through a built MouseEvent._

#### carries the single flip into the built MouseEvent

- carries the single flip into the built MouseEvent
   - Expected: ev.wheel equals `0 - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("carries the single flip into the built MouseEvent")
var b = offline_backend()
val ev = b.record_wheel(1)
expect(ev.wheel).to_equal(0 - 1)
```

</details>

#### carries a scroll-down detent as positive

- carries a scroll-down detent as positive
   - Expected: ev.wheel equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("carries a scroll-down detent as positive")
var b = offline_backend()
val ev = b.record_wheel(0 - 2)
expect(ev.wheel).to_equal(2)
```

</details>

#### clears the wheel after one event (one-shot detent)

- clears the wheel after one event (one-shot detent)
   - Expected: first.wheel equals `0 - 1`
   - Expected: second.wheel equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clears the wheel after one event (one-shot detent)")
var b = offline_backend()
val first = b.record_wheel(1)
expect(first.wheel).to_equal(0 - 1)
val second = b.record_mouse_position(0, 0)
expect(second.wheel).to_equal(0)
```

</details>

### availability honesty
_A backend with no live SDL2 window says so instead of polling into the void._

#### reports unavailable for a zero window handle

- reports unavailable for a zero window handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports unavailable for a zero window handle")
val b = Sdl2InputBackend.create(0)
assert_false(b.is_available())
```

</details>

#### explains why it is unavailable

- explains why it is unavailable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("explains why it is unavailable")
val b = Sdl2InputBackend.create(0)
expect(b.unavailable_reason()).to_contain("sdl2 window handle is 0")
```

</details>

#### reports available for a live window handle

- reports available for a live window handle
   - Expected: b.unavailable_reason() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports available for a live window handle")
val b = Sdl2InputBackend.create(42)
assert_true(b.is_available())
expect(b.unavailable_reason()).to_equal("")
```

</details>

#### create_unavailable preserves the caller's reason

- create_unavailable preserves the caller's reason
   - Expected: b.unavailable_reason() equals `SDL2 not built in`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("create_unavailable preserves the caller's reason")
val b = Sdl2InputBackend.create_unavailable("SDL2 not built in")
assert_false(b.is_available())
expect(b.unavailable_reason()).to_equal("SDL2 not built in")
```

</details>

### apply_mouse_button edges
_Edge-triggered button state, driven without SDL2._

#### reports a left press as pressed and just-pressed once

- reports a left press as pressed and just-pressed once


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports a left press as pressed and just-pressed once")
var b = offline_backend()
b.apply_mouse_button(0, true)
val ev = b.record_mouse_position(10, 20)
assert_true(ev.left_pressed)
assert_true(ev.left_just_pressed)
assert_false(ev.left_just_released)
```

</details>

#### does not repeat just-pressed while held

- does not repeat just-pressed while held


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not repeat just-pressed while held")
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

- reports a left release as just-released


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports a left release as just-released")
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

- tracks right and middle buttons independently of left


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("tracks right and middle buttons independently of left")
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

- marks mouse state as buffered


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("marks mouse state as buffered")
var b = offline_backend()
assert_false(b.has_buffered_mouse())
b.apply_mouse_button(0, true)
assert_true(b.has_buffered_mouse())
```

</details>

### record_mouse_position deltas
_Movement deltas are real, not hardcoded zeros._

#### reports real movement deltas, not zeros

- reports real movement deltas, not zeros
   - Expected: ev.x equals `13`
   - Expected: ev.y equals `7`
   - Expected: ev.dx equals `3`
   - Expected: ev.dy equals `0 - 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reports real movement deltas, not zeros")
var b = offline_backend()
b.record_mouse_position(10, 10)
val ev = b.record_mouse_position(13, 7)
expect(ev.x).to_equal(13)
expect(ev.y).to_equal(7)
expect(ev.dx).to_equal(3)
expect(ev.dy).to_equal(0 - 3)
```

</details>

### keysym translation
_SDL keysyms become distinct Key values, or nil when unmapped._

#### maps lowercase letters to distinct keys, not all to Key.A

- maps lowercase letters to distinct keys, not all to Key.A
   - Expected: b.key_to_char(ka) equals `a`
   - Expected: b.key_to_char(kz) equals `z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps lowercase letters to distinct keys, not all to Key.A")
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

- maps digits
   - Expected: b.key_to_char(k5) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps digits")
var b = offline_backend()
if val k5 = sdl2_keysym_to_key(53):
    expect(b.key_to_char(k5)).to_equal("5")
else:
    assert_true(false)
```

</details>

#### maps punctuation

- maps punctuation
   - Expected: b.key_to_char(kc) equals `,`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps punctuation")
var b = offline_backend()
if val kc = sdl2_keysym_to_key(44):
    expect(b.key_to_char(kc)).to_equal(",")
else:
    assert_true(false)
```

</details>

#### returns nil for an unmapped keysym rather than guessing

- returns nil for an unmapped keysym rather than guessing


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns nil for an unmapped keysym rather than guessing")
expect(sdl2_keysym_to_key(999999)).to_be_nil()
```

</details>

#### maps a scancode-derived navigation keysym

- maps a scancode-derived navigation keysym


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps a scancode-derived navigation keysym")
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

- yields lowercase with no modifiers
   - Expected: b.key_to_char(Key.A) equals `a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("yields lowercase with no modifiers")
var b = offline_backend()
expect(b.key_to_char(Key.A)).to_equal("a")
```

</details>

#### yields uppercase once SDL reports a shift modifier

- yields uppercase once SDL reports a shift modifier
   - Expected: b.key_to_char(Key.A) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("yields uppercase once SDL reports a shift modifier")
var b = offline_backend()
b.apply_key_mods(0x0003)
assert_true(b.shift_held())
expect(b.key_to_char(Key.A)).to_equal("A")
```

</details>

#### yields shifted punctuation

- yields shifted punctuation
   - Expected: b.key_to_char(Key.Num1) equals `!`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("yields shifted punctuation")
var b = offline_backend()
b.apply_key_mods(0x0003)
expect(b.key_to_char(Key.Num1)).to_equal("!")
```

</details>

#### adopts ctrl and alt from the SDL modifier bitfield

- adopts ctrl and alt from the SDL modifier bitfield


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("adopts ctrl and alt from the SDL modifier bitfield")
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

- returns nil for a key with no character


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("returns nil for a key with no character")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-WM-HOST-PLATFORM-003`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `884a005da7ad665f9c1128569de7e49fd0bf765ce95bfbce55d41f21b86334dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `884a005da7ad665f9c1128569de7e49fd0bf765ce95bfbce55d41f21b86334dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `884a005da7ad665f9c1128569de7e49fd0bf765ce95bfbce55d41f21b86334dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/compositor/hosted_input_sdl2_spec.spl
mirror: doc/06_spec/01_unit/os/compositor/hosted_input_sdl2_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/os/compositor/hosted_input_sdl2_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/compositor/hosted_input_sdl2_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/compositor/hosted_input_sdl2_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/compositor/hosted_input_sdl2_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/compositor/hosted_input_sdl2_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negates a scroll-up detent into positive-down' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/hosted_input_sdl2_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'negates a scroll-down detent into negative' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/compositor/hosted_input_sdl2_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves a zero detent alone' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

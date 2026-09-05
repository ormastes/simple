# Css Decl Apply Transform Specification

> Tests covering decl apply: display and position, decl apply: width and height, decl apply: margin expansion, decl apply: padding and border expansion, decl apply: background color, decl apply: font-size units, decl apply: flex, decl apply: transition and animation, decl apply: white-space, transform: translate, transform: scale, transform: rotate, transform: composition of multiple functions, transform: individual translate/scale/rotate properties, transform: origin, box, and style, transform: sticky interaction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 61 | 61 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Css Decl Apply Transform Specification

## Scenarios

### decl apply: display and position

#### display:flex applies

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- display:flex applies
   - Expected: probe("display:flex;", "display") equals `flex`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("display:flex applies")
expect(probe("display:flex;", "display")).to_equal("flex")
```

</details>

#### display:none applies

- display:none applies
   - Expected: probe("display:none;", "display") equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("display:none applies")
expect(probe("display:none;", "display")).to_equal("none")
```

</details>

#### position keywords map to the position flags

- position keywords map to the position flags
   - Expected: probe("position:relative;", "position") equals `relative`
   - Expected: probe("position:absolute;", "position") equals `absolute`
   - Expected: probe("position:sticky;", "position") equals `sticky`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("position keywords map to the position flags")
expect(probe("position:relative;", "position")).to_equal("relative")
expect(probe("position:absolute;", "position")).to_equal("absolute")
expect(probe("position:sticky;", "position")).to_equal("sticky")
```

</details>

#### later position:static resets an earlier relative

- later position:static resets an earlier relative
   - Expected: probe("position:relative;position:static;", "position") equals `static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("later position:static resets an earlier relative")
expect(probe("position:relative;position:static;", "position")).to_equal("static")
```

</details>

#### default position is static

- default position is static
   - Expected: probe("width:10px;", "position") equals `static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("default position is static")
expect(probe("width:10px;", "position")).to_equal("static")
```

</details>

### decl apply: width and height

#### px width and height apply

- px width and height apply
   - Expected: probe("width:150px;height:80px;", "width") equals `150`
   - Expected: probe("width:150px;height:80px;", "height") equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("px width and height apply")
expect(probe("width:150px;height:80px;", "width")).to_equal("150")
expect(probe("width:150px;height:80px;", "height")).to_equal("80")
```

</details>

#### percent width uses the negative-percent sentinel

- percent width uses the negative-percent sentinel
   - Expected: probe("width:50%;", "width") equals `-50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("percent width uses the negative-percent sentinel")
expect(probe("width:50%;", "width")).to_equal("-50")
```

</details>

#### longhand after longhand is last-wins

- longhand after longhand is last-wins
   - Expected: probe("width:100px;width:200px;", "width") equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("longhand after longhand is last-wins")
expect(probe("width:100px;width:200px;", "width")).to_equal("200")
```

</details>

### decl apply: margin expansion

#### one-value margin shorthand sets margin-left

- one-value margin shorthand sets margin-left
   - Expected: probe("margin:10px;", "margin_l") equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one-value margin shorthand sets margin-left")
expect(probe("margin:10px;", "margin_l")).to_equal("10")
```

</details>

#### four-value margin shorthand takes the fourth token for left

- four-value margin shorthand takes the fourth token for left
   - Expected: probe("margin:1px 2px 3px 4px;", "margin_l") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("four-value margin shorthand takes the fourth token for left")
expect(probe("margin:1px 2px 3px 4px;", "margin_l")).to_equal("4")
```

</details>

#### two-value margin shorthand takes the second token for left

- two-value margin shorthand takes the second token for left
   - Expected: probe("margin:5px 20px;", "margin_l") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two-value margin shorthand takes the second token for left")
expect(probe("margin:5px 20px;", "margin_l")).to_equal("20")
```

</details>

#### margin-left longhand applies and beats an earlier shorthand

- margin-left longhand applies and beats an earlier shorthand
   - Expected: probe("margin-left:30px;", "margin_l") equals `30`
   - Expected: probe("margin:10px;margin-left:33px;", "margin_l") equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("margin-left longhand applies and beats an earlier shorthand")
expect(probe("margin-left:30px;", "margin_l")).to_equal("30")
expect(probe("margin:10px;margin-left:33px;", "margin_l")).to_equal("33")
```

</details>

#### margin-left:auto resolves to 0

- margin-left:auto resolves to 0
   - Expected: probe("margin-left:auto;", "margin_l") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("margin-left:auto resolves to 0")
expect(probe("margin-left:auto;", "margin_l")).to_equal("0")
```

</details>

#### percent margin-left uses the negative-percent sentinel

- percent margin-left uses the negative-percent sentinel
   - Expected: probe("margin-left:25%;", "margin_l") equals `-25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("percent margin-left uses the negative-percent sentinel")
expect(probe("margin-left:25%;", "margin_l")).to_equal("-25")
```

</details>

### decl apply: padding and border expansion

#### one-value padding shorthand sets both left and right

- one-value padding shorthand sets both left and right
   - Expected: probe("padding:12px;", "pad_l") equals `12`
   - Expected: probe("padding:12px;", "pad_r") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("one-value padding shorthand sets both left and right")
expect(probe("padding:12px;", "pad_l")).to_equal("12")
expect(probe("padding:12px;", "pad_r")).to_equal("12")
```

</details>

#### four-value padding shorthand splits left and right

- four-value padding shorthand splits left and right
   - Expected: probe("padding:1px 2px 3px 4px;", "pad_l") equals `4`
   - Expected: probe("padding:1px 2px 3px 4px;", "pad_r") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("four-value padding shorthand splits left and right")
expect(probe("padding:1px 2px 3px 4px;", "pad_l")).to_equal("4")
expect(probe("padding:1px 2px 3px 4px;", "pad_r")).to_equal("2")
```

</details>

#### padding-left longhand applies

- padding-left longhand applies
   - Expected: probe("padding-left:7px;", "pad_l") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("padding-left longhand applies")
expect(probe("padding-left:7px;", "pad_l")).to_equal("7")
```

</details>

#### border shorthand sets border-left width

- border shorthand sets border-left width
   - Expected: probe("border:3px solid #ff0000;", "border_l") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border shorthand sets border-left width")
expect(probe("border:3px solid #ff0000;", "border_l")).to_equal("3")
```

</details>

#### border-left shorthand sets border-left width

- border-left shorthand sets border-left width
   - Expected: probe("border-left:5px solid #000000;", "border_l") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("border-left shorthand sets border-left width")
expect(probe("border-left:5px solid #000000;", "border_l")).to_equal("5")
```

</details>

### decl apply: background color

#### background-color hex parses to ARGB

- background-color hex parses to ARGB
   - Expected: probe("background-color:#ff0000;", "background_color") equals `4294901760`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("background-color hex parses to ARGB")
# opaque red = 0xFFFF0000 = 4294901760
expect(probe("background-color:#ff0000;", "background_color")).to_equal("4294901760")
```

</details>

#### background shorthand color parses to ARGB

- background shorthand color parses to ARGB
   - Expected: probe("background:#0000ff;", "background_color") equals `4278190335`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("background shorthand color parses to ARGB")
# opaque blue = 0xFF0000FF = 4278190335
expect(probe("background:#0000ff;", "background_color")).to_equal("4278190335")
```

</details>

#### longhand background-color after shorthand wins

- longhand background-color after shorthand wins
   - Expected: probe("background:#0000ff;background-color:#ff0000;", "background_color") equals `4294901760`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("longhand background-color after shorthand wins")
expect(probe("background:#0000ff;background-color:#ff0000;", "background_color")).to_equal("4294901760")
```

</details>

### decl apply: font-size units

#### px font-size applies

- px font-size applies
   - Expected: probe("font-size:24px;", "font_size") equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("px font-size applies")
expect(probe("font-size:24px;", "font_size")).to_equal("24")
```

</details>

#### em font-size resolves against the inherited base

- em font-size resolves against the inherited base
   - Expected: probe("font-size:2em;", "font_size") equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("em font-size resolves against the inherited base")
expect(probe("font-size:2em;", "font_size")).to_equal("32")
```

</details>

#### rem font-size resolves against the 16px root

- rem font-size resolves against the 16px root
   - Expected: probe("font-size:1.5rem;", "font_size") equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rem font-size resolves against the 16px root")
expect(probe("font-size:1.5rem;", "font_size")).to_equal("24")
```

</details>

#### percent font-size resolves against the inherited base

- percent font-size resolves against the inherited base
   - Expected: probe("font-size:150%;", "font_size") equals `24`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("percent font-size resolves against the inherited base")
expect(probe("font-size:150%;", "font_size")).to_equal("24")
```

</details>

### decl apply: flex

#### flex-direction:column applies

- flex-direction:column applies
   - Expected: probe("display:flex;flex-direction:column;", "flex_direction") equals `column`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flex-direction:column applies")
expect(probe("display:flex;flex-direction:column;", "flex_direction")).to_equal("column")
```

</details>

#### flex-grow longhand applies

- flex-grow longhand applies
   - Expected: probe("flex-grow:3;", "flex_grow") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flex-grow longhand applies")
expect(probe("flex-grow:3;", "flex_grow")).to_equal("3")
```

</details>

#### flex-wrap:wrap applies

- flex-wrap:wrap applies
   - Expected: probe("display:flex;flex-wrap:wrap;", "flex_wrap") equals `wrap`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flex-wrap:wrap applies")
expect(probe("display:flex;flex-wrap:wrap;", "flex_wrap")).to_equal("wrap")
```

</details>

### decl apply: transition and animation

#### transition shorthand extracts property and duration

- transition shorthand extracts property and duration
   - Expected: probe("transition:width 0.3s;", "transition_property") equals `width`
   - Expected: probe("transition:width 0.3s;", "transition_duration_ms") equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transition shorthand extracts property and duration")
expect(probe("transition:width 0.3s;", "transition_property")).to_equal("width")
expect(probe("transition:width 0.3s;", "transition_duration_ms")).to_equal("300")
```

</details>

#### transition-duration longhand applies in ms

- transition-duration longhand applies in ms
   - Expected: probe("transition-duration:250ms;", "transition_duration_ms") equals `250`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transition-duration longhand applies in ms")
expect(probe("transition-duration:250ms;", "transition_duration_ms")).to_equal("250")
```

</details>

#### animation shorthand extracts name and duration

- animation shorthand extracts name and duration
   - Expected: probe("animation:spin 2s linear;", "animation_name") equals `spin`
   - Expected: probe("animation:spin 2s linear;", "animation_duration_ms") equals `2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("animation shorthand extracts name and duration")
expect(probe("animation:spin 2s linear;", "animation_name")).to_equal("spin")
expect(probe("animation:spin 2s linear;", "animation_duration_ms")).to_equal("2000")
```

</details>

#### animation-iteration-count:infinite applies

- animation-iteration-count:infinite applies
   - Expected: probe("animation-iteration-count:infinite;", "animation_iteration_count") equals `infinite`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("animation-iteration-count:infinite applies")
expect(probe("animation-iteration-count:infinite;", "animation_iteration_count")).to_equal("infinite")
```

</details>

### decl apply: white-space

#### white-space:nowrap sets the nowrap flag

- white-space:nowrap sets the nowrap flag
   - Expected: probe("white-space:nowrap;", "white_space_nowrap") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("white-space:nowrap sets the nowrap flag")
expect(probe("white-space:nowrap;", "white_space_nowrap")).to_equal("true")
```

</details>

#### white-space:normal leaves nowrap off

- white-space:normal leaves nowrap off
   - Expected: probe("white-space:normal;", "white_space_nowrap") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("white-space:normal leaves nowrap off")
expect(probe("white-space:normal;", "white_space_nowrap")).to_equal("false")
```

</details>

### transform: translate

#### transform translate(x, y) promotes the node to relative positioning

- transform translate(x, y) promotes the node to relative positioning
   - Expected: probe("transform:translate(30px, 40px);", "position") equals `relative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform translate(x, y) promotes the node to relative positioning")
expect(probe("transform:translate(30px, 40px);", "position")).to_equal("relative")
```

</details>

#### transform translateX alone promotes to relative

- transform translateX alone promotes to relative
   - Expected: probe("transform:translateX(15px);", "position") equals `relative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform translateX alone promotes to relative")
expect(probe("transform:translateX(15px);", "position")).to_equal("relative")
```

</details>

#### negative translate offsets still promote to relative

- negative translate offsets still promote to relative
   - Expected: probe("transform:translate(-10px, -5px);", "position") equals `relative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negative translate offsets still promote to relative")
expect(probe("transform:translate(-10px, -5px);", "position")).to_equal("relative")
```

</details>

#### zero translate does not change positioning

- zero translate does not change positioning
   - Expected: probe("transform:translate(0px, 0px);", "position") equals `static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("zero translate does not change positioning")
expect(probe("transform:translate(0px, 0px);", "position")).to_equal("static")
```

</details>

#### transform:none is a no-op

- transform:none is a no-op
   - Expected: probe("transform:none;", "position") equals `static`
   - Expected: probe("width:100px;transform:none;", "width") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform:none is a no-op")
expect(probe("transform:none;", "position")).to_equal("static")
expect(probe("width:100px;transform:none;", "width")).to_equal("100")
```

</details>

### transform: scale

#### transform scale(2) doubles width and height

- transform scale(2) doubles width and height
   - Expected: probe("width:100px;height:50px;transform:scale(2);", "width") equals `200`
   - Expected: probe("width:100px;height:50px;transform:scale(2);", "height") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform scale(2) doubles width and height")
expect(probe("width:100px;height:50px;transform:scale(2);", "width")).to_equal("200")
expect(probe("width:100px;height:50px;transform:scale(2);", "height")).to_equal("100")
```

</details>

#### transform scale with a percent argument applies proportionally

- transform scale with a percent argument applies proportionally
   - Expected: probe("width:100px;transform:scale(150%);", "width") equals `150`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform scale with a percent argument applies proportionally")
expect(probe("width:100px;transform:scale(150%);", "width")).to_equal("150")
```

</details>

#### scale(1) leaves the size unchanged

- scale(1) leaves the size unchanged
   - Expected: probe("width:100px;transform:scale(1);", "width") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scale(1) leaves the size unchanged")
expect(probe("width:100px;transform:scale(1);", "width")).to_equal("100")
```

</details>

#### scale does not apply to a node without an explicit positive size

- scale does not apply to a node without an explicit positive size
   - Expected: probe("width:50%;transform:scale(2);", "width") equals `-50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scale does not apply to a node without an explicit positive size")
expect(probe("width:50%;transform:scale(2);", "width")).to_equal("-50")
```

</details>

### transform: rotate

#### rotate(90deg) swaps width and height

- rotate(90deg) swaps width and height
   - Expected: probe("width:100px;height:40px;transform:rotate(90deg);", "width") equals `40`
   - Expected: probe("width:100px;height:40px;transform:rotate(90deg);", "height") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotate(90deg) swaps width and height")
expect(probe("width:100px;height:40px;transform:rotate(90deg);", "width")).to_equal("40")
expect(probe("width:100px;height:40px;transform:rotate(90deg);", "height")).to_equal("100")
```

</details>

#### rotate(270deg) also swaps width and height

- rotate(270deg) also swaps width and height
   - Expected: probe("width:100px;height:40px;transform:rotate(270deg);", "width") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotate(270deg) also swaps width and height")
expect(probe("width:100px;height:40px;transform:rotate(270deg);", "width")).to_equal("40")
```

</details>

#### rotate(180deg) is not a quarter turn and does not swap

- rotate(180deg) is not a quarter turn and does not swap
   - Expected: probe("width:100px;height:40px;transform:rotate(180deg);", "width") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotate(180deg) is not a quarter turn and does not swap")
expect(probe("width:100px;height:40px;transform:rotate(180deg);", "width")).to_equal("100")
```

</details>

#### rotate(450deg) normalizes to a quarter turn and swaps

- rotate(450deg) normalizes to a quarter turn and swaps
   - Expected: probe("width:100px;height:40px;transform:rotate(450deg);", "width") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotate(450deg) normalizes to a quarter turn and swaps")
expect(probe("width:100px;height:40px;transform:rotate(450deg);", "width")).to_equal("40")
```

</details>

### transform: composition of multiple functions

#### translate + scale + rotate compose: relative, scaled, then swapped

- translate + scale + rotate compose: relative, scaled, then swapped
   - Expected: probe(css, "position") equals `relative`
   - Expected: probe(css, "width") equals `80`
   - Expected: probe(css, "height") equals `200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translate + scale + rotate compose: relative, scaled, then swapped")
val css = "width:100px;height:40px;transform:translate(10px, 5px) scale(2) rotate(90deg);"
expect(probe(css, "position")).to_equal("relative")
# scale first (200 x 80), then quarter-turn swap (80 x 200)
expect(probe(css, "width")).to_equal("80")
expect(probe(css, "height")).to_equal("200")
```

</details>

### transform: individual translate/scale/rotate properties

#### translate property promotes to relative

- translate property promotes to relative
   - Expected: probe("translate:10px 20px;", "position") equals `relative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translate property promotes to relative")
expect(probe("translate:10px 20px;", "position")).to_equal("relative")
```

</details>

#### translate:none is a no-op

- translate:none is a no-op
   - Expected: probe("translate:none;", "position") equals `static`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("translate:none is a no-op")
expect(probe("translate:none;", "position")).to_equal("static")
```

</details>

#### scale property scales width and height

- scale property scales width and height
   - Expected: probe("width:100px;height:50px;scale:2;", "width") equals `200`
   - Expected: probe("width:100px;height:50px;scale:2;", "height") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("scale property scales width and height")
expect(probe("width:100px;height:50px;scale:2;", "width")).to_equal("200")
expect(probe("width:100px;height:50px;scale:2;", "height")).to_equal("100")
```

</details>

#### rotate property quarter turn swaps width and height

- rotate property quarter turn swaps width and height
   - Expected: probe("width:100px;height:40px;rotate:90deg;", "width") equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotate property quarter turn swaps width and height")
expect(probe("width:100px;height:40px;rotate:90deg;", "width")).to_equal("40")
```

</details>

#### rotate property non-quarter turn does not swap

- rotate property non-quarter turn does not swap
   - Expected: probe("width:100px;height:40px;rotate:45deg;", "width") equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rotate property non-quarter turn does not swap")
expect(probe("width:100px;height:40px;rotate:45deg;", "width")).to_equal("100")
```

</details>

### transform: origin, box, and style

#### transform-origin stores the normalized value

- transform-origin stores the normalized value
   - Expected: probe("transform-origin:top left;", "transform_origin") equals `top left`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform-origin stores the normalized value")
expect(probe("transform-origin:top left;", "transform_origin")).to_equal("top left")
```

</details>

#### transform-box accepts the box keywords

- transform-box accepts the box keywords
   - Expected: probe("transform-box:fill-box;", "transform_box") equals `fill-box`
   - Expected: probe("transform-box:border-box;", "transform_box") equals `border-box`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform-box accepts the box keywords")
expect(probe("transform-box:fill-box;", "transform_box")).to_equal("fill-box")
expect(probe("transform-box:border-box;", "transform_box")).to_equal("border-box")
```

</details>

#### invalid transform-box is rejected (matches the untouched default)

- invalid transform-box is rejected (matches the untouched default)
   - Expected: probe("transform-box:banana;", "transform_box") equals `control`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid transform-box is rejected (matches the untouched default)")
val control = probe("width:10px;", "transform_box")
expect(probe("transform-box:banana;", "transform_box")).to_equal(control)
```

</details>

#### transform-style accepts flat and preserve-3d

- transform-style accepts flat and preserve-3d
   - Expected: probe("transform-style:preserve-3d;", "transform_style") equals `preserve-3d`
   - Expected: probe("transform-style:flat;", "transform_style") equals `flat`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform-style accepts flat and preserve-3d")
expect(probe("transform-style:preserve-3d;", "transform_style")).to_equal("preserve-3d")
expect(probe("transform-style:flat;", "transform_style")).to_equal("flat")
```

</details>

#### invalid transform-style is rejected (matches the untouched default)

- invalid transform-style is rejected (matches the untouched default)
   - Expected: probe("transform-style:diagonal;", "transform_style") equals `control`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("invalid transform-style is rejected (matches the untouched default)")
val control = probe("width:10px;", "transform_style")
expect(probe("transform-style:diagonal;", "transform_style")).to_equal(control)
```

</details>

### transform: sticky interaction

#### a transform on a sticky node keeps sticky positioning

- a transform on a sticky node keeps sticky positioning
   - Expected: probe("position:sticky;transform:translate(10px, 10px);", "position") equals `sticky`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a transform on a sticky node keeps sticky positioning")
expect(probe("position:sticky;transform:translate(10px, 10px);", "position")).to_equal("sticky")
```

</details>

#### transform:none on a sticky node keeps sticky positioning

- transform:none on a sticky node keeps sticky positioning
   - Expected: probe("position:sticky;transform:none;", "position") equals `sticky`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transform:none on a sticky node keeps sticky positioning")
expect(probe("position:sticky;transform:none;", "position")).to_equal("sticky")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering decl apply: display and position, decl apply: width and height, decl apply: margin expansion, decl apply: padding and border expansion, decl apply: background color, decl apply: font-size units, decl apply: flex, decl apply: transition and animation, decl apply: white-space, transform: translate, transform: scale, transform: rotate, transform: composition of multiple functions, transform: individual translate/scale/rotate properties, transform: origin, box, and style, transform: sticky interaction.
- decl apply: display and position
- decl apply: width and height
- decl apply: margin expansion
- decl apply: padding and border expansion
- decl apply: background color
- decl apply: font-size units
- decl apply: flex
- decl apply: transition and animation
- decl apply: white-space
- transform: translate
- transform: scale
- transform: rotate
- transform: composition of multiple functions
- transform: individual translate/scale/rotate properties
- transform: origin, box, and style
- transform: sticky interaction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 61 |
| Active scenarios | 61 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d47dc28eeb3b210764382a8c0f53d488262ac937fab5f695316d690eff050844`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d47dc28eeb3b210764382a8c0f53d488262ac937fab5f695316d690eff050844`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d47dc28eeb3b210764382a8c0f53d488262ac937fab5f695316d690eff050844`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'display:flex applies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'display:none applies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/css_decl_apply_transform_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'position keywords map to the position flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

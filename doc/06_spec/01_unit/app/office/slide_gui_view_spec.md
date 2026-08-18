# slide_gui_view_spec

> Slide GUI view + presenter session spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# slide_gui_view_spec

Slide GUI view + presenter session spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slide_gui_view_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Slide GUI view + presenter session spec.

slide_gui_view(deck, slide_index) renders ONE slide of a deck (the [Slide]
list deck_format.spl's parse_deck returns) as a GUI widget tree -- title +
bullets as text widgets (bullets indented per nesting level), tables/images
as honest placeholder text lines -- plus a plain-text pipe-separated dump:
"slide|<index+1>/<total>|<title>" first, then one line per element
("bullet|<level>|<text>", "text|<text>", "table|<rows>x<cols>",
"image|<alt>"). An out-of-range slide index fails closed with an
"error|bad-index" line instead of crashing.

SlideGuiSession navigates the deck: slide_session_next/prev clamp at the
ends, slide_session_goto is 1-based and fails closed (last_error
"bad-index") on out-of-range targets, and slide_gui_step maps presenter
keys: "n"/"right"/"space" next, "p"/"left" prev, single digits "1".."9"
goto, "q"/"ctrl_c"/"eof" quit.

The live presenter loop (`office slides-gui-live`, interactive.spl's
run_slides_gui_live) feeds decode_key_byte key names through the pure
slides_live_map_key translation before slide_gui_step: right -> "n",
left -> "p", a decoded space (" " or "space") -> "n", n/p/digits/quit keys
pass through, anything else -> "" (no step).

## Scenarios

### slide_gui_view: header line
_The dump always starts with slide|<index+1>/<total>|<title>._

#### the first line carries the 1-based slide number, total, and title

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
val view = slide_gui_view(deck, 0)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("slide|1/4|Intro")
```

</details>

#### a later slide's header carries its own 1-based position

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
val view = slide_gui_view(deck, 2)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("slide|3/4|Results")
```

</details>

### slide_gui_view: bullets

#### bullets render one line each with their nesting level, in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
val view = slide_gui_view(deck, 1)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("slide|2/4|Agenda")
expect(lines[1]).to_equal("bullet|0|First point")
expect(lines[2]).to_equal("bullet|1|Nested detail")
expect(lines[3]).to_equal("bullet|0|Second point")
```

</details>

### slide_gui_view: plain body text
_A non-bullet body text box renders as a text|<content> line._

#### a body text box renders its content on a text| line

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = _titled_slide("s1", "Notes")
s = add_text_box(s, "body1", "Plain body line", 60, 220, 840, 80)
var deck: [Slide] = []
deck.push(s)
val view = slide_gui_view(deck, 0)
val lines = view.text_dump.split("\n")
expect(lines[0]).to_equal("slide|1/1|Notes")
expect(lines[1]).to_equal("text|Plain body line")
```

</details>

### slide_gui_view: table placeholder

#### a table element renders as table|<rows>x<cols>

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
val view = slide_gui_view(deck, 2)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("table|3x2")
```

</details>

### slide_gui_view: image placeholder

#### an image element renders its alt text on an image| line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
val view = slide_gui_view(deck, 3)
val lines = view.text_dump.split("\n")
expect(lines[1]).to_equal("image|architecture")
```

</details>

### slide_gui_view: bad index fails closed
_An out-of-range slide index produces an error line, no crash._

#### an index past the deck end produces error|bad-index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
val view = slide_gui_view(deck, 9)
expect(view.text_dump).to_contain("error|bad-index")
```

</details>

#### a negative index produces error|bad-index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
val view = slide_gui_view(deck, -1)
expect(view.text_dump).to_contain("error|bad-index")
```

</details>

### SlideGuiSession: next/prev clamp

#### next advances and clamps at the last slide

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
expect(session.current_index).to_equal(0)
session = slide_session_next(session)
expect(session.current_index).to_equal(1)
session = slide_session_next(session)
session = slide_session_next(session)
expect(session.current_index).to_equal(3)
session = slide_session_next(session)
expect(session.current_index).to_equal(3)
expect(session.last_error).to_equal("")
```

</details>

#### prev at the first slide clamps to the first slide

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
session = slide_session_prev(session)
expect(session.current_index).to_equal(0)
expect(session.last_error).to_equal("")
```

</details>

### SlideGuiSession: goto

#### goto jumps to the 1-based slide and clears last_error

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
session = slide_session_goto(session, 3)
expect(session.current_index).to_equal(2)
expect(session.last_error).to_equal("")
```

</details>

#### goto past the deck end leaves the index unchanged and records bad-index

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
session = slide_session_goto(session, 9)
expect(session.current_index).to_equal(0)
expect(session.last_error).to_equal("bad-index")
```

</details>

#### goto 0 is out of range for a 1-based target

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
session = slide_session_goto(session, 0)
expect(session.current_index).to_equal(0)
expect(session.last_error).to_equal("bad-index")
```

</details>

### slide_gui_step: key mapping

#### n, right, and space each advance one slide

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
var res = slide_gui_step(session, "n")
session = res.session
expect(session.current_index).to_equal(1)
res = slide_gui_step(session, "right")
session = res.session
expect(session.current_index).to_equal(2)
res = slide_gui_step(session, "space")
session = res.session
expect(session.current_index).to_equal(3)
assert_false(res.quit)
```

</details>

#### p and left each step back one slide

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
session = slide_session_goto(session, 3)
var res = slide_gui_step(session, "p")
session = res.session
expect(session.current_index).to_equal(1)
res = slide_gui_step(session, "left")
session = res.session
expect(session.current_index).to_equal(0)
assert_false(res.quit)
```

</details>

#### a digit key jumps to that 1-based slide

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
var res = slide_gui_step(session, "4")
session = res.session
expect(session.current_index).to_equal(3)
assert_false(res.quit)
```

</details>

#### an out-of-range digit key fails closed with bad-index

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
var res = slide_gui_step(session, "9")
session = res.session
expect(session.current_index).to_equal(0)
expect(session.last_error).to_equal("bad-index")
assert_false(res.quit)
```

</details>

#### q, ctrl_c, and eof signal quit with the session unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
session = slide_session_goto(session, 2)
val res_q = slide_gui_step(session, "q")
assert_true(res_q.quit)
expect(res_q.session.current_index).to_equal(1)
val res_c = slide_gui_step(session, "ctrl_c")
assert_true(res_c.quit)
val res_e = slide_gui_step(session, "eof")
assert_true(res_e.quit)
expect(res_e.session.current_index).to_equal(1)
```

</details>

#### an unknown key is a no-op

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val deck = _demo_deck()
var session = slide_session_new(deck)
val res = slide_gui_step(session, "z")
expect(res.session.current_index).to_equal(0)
assert_false(res.quit)
```

</details>

### live presenter step

#### right maps to n (next)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(slides_live_map_key("right")).to_equal("n")
```

</details>

#### left maps to p (prev)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(slides_live_map_key("left")).to_equal("p")
```

</details>

#### a decoded space (the ' ' printable byte 32) maps to n

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(slides_live_map_key(" ")).to_equal("n")
```

</details>

#### the canonical space name also maps to n

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(slides_live_map_key("space")).to_equal("n")
```

</details>

#### a digit passes through for 1-based goto

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(slides_live_map_key("3")).to_equal("3")
```

</details>

#### n and p pass through unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(slides_live_map_key("n")).to_equal("n")
expect(slides_live_map_key("p")).to_equal("p")
```

</details>

#### q, ctrl_c, and eof pass through as quit keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(slides_live_map_key("q")).to_equal("q")
expect(slides_live_map_key("ctrl_c")).to_equal("ctrl_c")
expect(slides_live_map_key("eof")).to_equal("eof")
```

</details>

#### unknown keys map to the empty no-step key

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(slides_live_map_key("z")).to_equal("")
expect(slides_live_map_key("escape")).to_equal("")
expect(slides_live_map_key("0")).to_equal("")
expect(slides_live_map_key("")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

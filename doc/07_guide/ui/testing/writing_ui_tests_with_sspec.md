# Writing UI Tests with SSpec

**Audience:** an agent or developer who has been asked to "add a UI test" in this
repo and needs to know which layer to test at, what actually runs here, and which
traps will make a correct implementation look broken.

**TL;DR**

- Test `src/lib/common/ui/**` **directly, with no display**. That is the right
  answer for nearly every UI test, and it is orders of magnitude cheaper.
- The `play_*` MCP tools drive a *live* window. Nothing in this tree sets up a
  virtual display, so those lanes are unverified here — see §3.
- Spec bodies run **interpreted**, where binding a class-typed element out of a
  collection and mutating it silently loses the write. This is the single most
  common way a UI spec goes RED while the code under test is correct (§4.1).
- Exit 0 is not a pass. Require the `Results:` line.

---

## 1. What SSpec is here

SSpec is the in-tree spec DSL, implemented in
`src/lib/nogc_sync_mut/spec.spl` and imported as `use std.spec.*` (or
`use std.spec`). It is RSpec-shaped:

| Surface | Where |
|---|---|
| `describe` / `context` | `spec.spl:81`, `:94` |
| `it` / `test` / `example` / `specify` | `spec.spl:153,158,161,164` |
| `step(description)` | `spec.spl:167` |
| `before_each` / `after_each` / `before_all` / `after_all` | `spec.spl:590,593,617,620` |
| `expect(value)` (bool and generic overloads) | `spec.spl:696`, `:701` |
| `assert_true` / `assert_false` / `assert_equal` / `assert_contains` / … | `spec.spl:1056,1060,1072,1080` |
| `pending(name)` | `spec.spl:242` |
| Environment gates: `only_on_linux`, `skip_on_interpreter`, `skip_if_missing_module`, … | `spec.spl:384-526` |

`pending(name)` is **not** a free escape hatch: it validates against the active
assurance profile (`validate_bare_pending(_active_assurance_profile())`,
`spec.spl:243`) and, when the profile disallows a bare pending, pushes an error
into the enclosing `it`'s error list so it is accounted exactly like a real
assertion failure. Do not reach for it to quiet a red UI spec — per
`.claude/rules/testing.md`, a correct spec that fails is a legitimate artifact:
leave it red and file a `doc/08_tracking/bug/` record.

**A UI spec is not a different kind of spec.** There is no `describe_ui`, no UI
runner mode, no display-aware harness in the DSL. The only thing that makes a
spec a "UI test" is *what it imports*. That is why the layer you choose (§2)
decides essentially everything about cost and reliability.

Matchers: `to_equal`, `to_be`, `to_be_nil`, `to_be_truthy`, `to_be_falsy`,
`to_contain`, `to_start_with`, `to_end_with`, `to_be_greater_than`,
`to_be_less_than`. `to_be_true` / `to_be_false` are **rejected** on bool
receivers — use `assert_true` / `assert_false` or `.to_equal(true)`.

---

## 2. The UI surfaces, and which to pick

### 2a. Model / layout / style logic — no display (pick this)

`src/lib/common/ui/**` is 160 `.spl` modules of draw-IR, scene, widget, theme and
CSS logic that is data-in / data-out. You call the function and assert on the
returned value. No window, no compositor, no MCP, no timing.

Real example, `test/01_unit/lib/common/ui/pixel_surface_content_frame_spec.spl`:

```simple
# @cover src/lib/common/ui/pixel_surface_content_frame.spl 20%
use std.spec
use common.ui.pixel_surface_content_frame.{pixel_surface_content_frame}
use common.ui.window_scene.{WM_CONTENT_ORIGIN_PIXEL_SURFACE}

describe "pixel surface content frame":
    it "validates pixels and retains nested placement":
        val frame = pixel_surface_content_frame(
            "canvas", "1", 7, 9, 2, 2,
            [0xff000001u32, 0xff000002u32, 0xff000003u32, 0xff000004u32],
            3, 4
        )
        expect(frame.origin_kind).to_equal(WM_CONTENT_ORIGIN_PIXEL_SURFACE)
        expect(frame.offset_x).to_equal(7)
```

That spec asserts on real pixel data and needs nothing but the interpreter.
Note also `src/lib/common/ui/x11_backend_gate.spl`: it is a **pure text gate** —
functions taking `text` and returning `text` that check declared feature
strings. It does not open X11, so it is unit-testable with no display.

**Rule of thumb: if you can phrase the question as "given this scene/theme/state,
what does the layer compute?", it belongs here.** Almost all UI questions can be.

### 2b. Live-window drivers — MCP `play_*` tools

These are agent-facing MCP tools, not spec functions. You cannot call them from
a `.spl` spec body; an agent invokes them out-of-band. Implemented in
`src/app/mcp/{tool_table,main_lazy_play_tools,main_dispatch,main_static_tools}.spl`.

| Family | Count | Use for |
|---|---|---|
| `play_*` (`play_launch`, `play_click`, `play_fill`, `play_screenshot`, …) | 11 | browser-hosted UI |
| `play_ui_*` (`connect`, `ensure`, `query`, `snapshot`, `act`) | 5 | the in-tree UI harness protocol |
| `play_wm_*` (`list`, `click`, `type`, `screenshot`, `text_find`, `text_act`, `text_snapshot`, `text_status`) | 8 | the window manager / hosted WM |
| `play_sdl2_*` (`connect`, `elements`, `click`, `fill`, `screenshot`) | 5 | the SDL2 lane |
| `debug_ui_widget_tree`, `debug_ui_css_dump`, `debug_ui_theme_tokens` | 3 | inspecting a *running* UI's tree/CSS/tokens |

There is also an in-Simple client for the harness protocol,
`src/lib/nogc_sync_mut/ui_test/client.spl` — `UITestClient.connect(host, port)`
(`:57`), then `click`, `type_text`, `drag`, `send_key`, `submit`, `focus_next`,
`get_element`, `get_elements`, `get_state`, `screenshot_html`, `check_text`,
`check_visible`, `check_focused`, `check_exists`, `check_enabled`,
`check_selected`, `wait_for(id, timeout_ms)`, `wait_ready(timeout_ms)`
(`client.spl:85-352`). Every method returns `Result<…, text>`, so a spec using it
must handle the error arm — a failed connect is not a pass.

`debug_ui_*` require an attached session; they inspect a live process, not source.

**Cost comparison is not close.** 2b needs a display, a running app, a live
connection, and timing tolerance; each of those is an independent way to get a
flaky or inconclusive result. 2a needs a function call. Prefer 2a unless the
thing you are testing genuinely only exists at the window boundary.

---

## 3. Headless reality — read this before writing a live-window test

**The unit layer runs headless. The live-window layer is unconfirmed here, and
there is no virtual-display setup in the tree.**

Evidence for headless working:

- `os.compositor.host_compositor_core.HeadlessHostCompositorBackend` is a
  first-class seam, and
  `test/03_system/gui/wm_host_platform/wm_host_runtime_linux_spec.spl:27-28`
  states it is the headless seam implementation that every live backend shares.
  That spec asserts on real pixel buffers with no display attached.
- `src/lib/common/ui/x11_backend_gate.spl` never touches X11 (§2a).
- The bulk of `common/ui` is IR/model/serialisation.

Evidence for the gap — state it plainly rather than guessing:

- **No `xvfb`, no `SDL_VIDEODRIVER=dummy`, no `DISPLAY=` setup exists anywhere
  under `test/03_system/gui/` or the `scripts/check/*gui*` / `*wm*` scripts**
  (grep: zero hits). The SDL editor lane (`editor_gui_sdl_spec.spl`), the hosted
  WM lane (`linux_hosted_wm_live_window_spec.spl`) and the QEMU capture lane
  (`qemu_gtk_wm_capture_evidence_spec.spl`) all appear to assume a real display
  or a QEMU guest.

So: **if your test needs a window, this environment probably cannot run it, and
nothing in the tree will tell you that — it will read as environmental noise.**
Write at layer 2a, or declare the environmental dependency explicitly in the
spec and in your report.

Related known gaps: the WM compare lane has only **4** `.ppm` goldens
(`test/03_system/gui/wm_compare/goldens/`) with no provenance note beside them,
and only ~14 files in the whole tree reference any `play_ui_*` / `play_wm_*` /
`play_sdl2_*` name against 29 such tools. Do not assume a `play_*` path is
exercised just because it exists.

---

## 4. The traps

These are the part of this guide that will actually save you time. Every one was
observed in this repo.

### 4.1 Spec bodies run interpreted, and element-mutation silently no-ops

`bin/simple test` hard-defaults to the tree-walk interpreter. Under the
interpreter, reading a **class-typed** element out of a collection returns a
**copy**, so mutating the binding throws the write away with no error:

```simple
val node = tree.children[i]   # interpreter: node is a COPY
node.visible = false          # write is LOST; tree.children[i] is unchanged
```

Bug record: `doc/08_tracking/bug/interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`
(`Value::ClassInstance` has zero producers).

This is how a spec goes RED while the code under test is correct. It happened
today: in `test/01_unit/app/office/cursor_hidden_row_invariant_spec.spl` the
fixture did `val sh = app.workbook.active()` then `sh.hide_row(r)` — and
`Workbook.active()` is `me.sheets[me.active_sheet]`
(`src/app/office/sheets/spreadsheet.spl:245-247`), a class-typed list-element
read. The app's real sheet therefore had **no hidden rows at all**; the
navigation code was sound and the spec was testing a throwaway. Full analysis:
`scratchpad/sessions/red_spec_disposition.md`.

A UI fixture that builds a widget/scene tree and then mutates nodes fetched out
of a children list is exactly this shape. Mitigations: mutate through the owner
(`tree.set_child(i, …)` / a method on the container), keep fixtures
build-then-return (construct the final value; do not post-mutate), or use structs
rather than classes for fixture nodes. Good news for `src/lib/common/ui/**`
specifically: a scan of all 175 UI modules found **0** bind-then-mutate sites —
the layer is predominantly functional (226 structs to 112 classes). The risk is
in *your fixture*, not in the library.

### 4.2 Exit 0 is not a pass

`bin/simple test <spec>` has been measured printing ~1897 lines of warnings with
**zero** pass/fail/total lines and exiting **0**
(`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`).
Require an explicit `Results: N total, N passed, N failed` line in the captured
output. No `Results:` line ⇒ **INCONCLUSIVE**, never green. Also: take `$?` from
the command under test, never from a pipe — a pipe reports `tail`'s status.

### 4.3 Never wrap a spec run in `timeout`

A killed run emits no `Results:` line, so it proves nothing — it is strictly
worse than not running. If a spec is too slow to finish, that is a finding to
report, not something to truncate.

### 4.4 Record the binary identity before *and* after

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
```

The symlink target is replaced by other lanes mid-session — **three distinct
builds were seen in one day**. A run that spans a swap is inconclusive
regardless of what it printed. Capture the pair before the run and again after,
and only claim a result if they match.

### 4.5 Prefer per-path absolute expected values over relative oracles

A relative oracle — `expect(rows[2]).to_equal(rows[0])` — makes **one** broken
path present as **many** failures spread across unrelated assertions, and points
the reader at the wrong path. This exact design cost a misdiagnosis today: in
the office cursor spec the failures at `:109`, `:115`, `:121` were all the same
single defective element compared against a healthy one, which read as
"the shared invariant is broken" when it was one fixture bug.

Write instead:

```simple
expect(gui_row).to_equal(2)
expect(tui_row).to_equal(2)
expect(app_row).to_equal(2)
```

Each path gets its own absolute expectation, each failure names its own path,
and a break in one does not smear across the others.

### 4.6 A scanner-style spec needs a positive control

If your spec scans source or a widget tree looking for a bad shape, a clean
sweep is ambiguous: the code may be fine, or your scanner may be broken. Pair
every absence check with a control that MUST produce a hit. Good example:
`test/01_unit/app/argv_entry_script_suffix_heuristic_class_spec.spl:40,46` —
`it "control: the detector fires on the defective shape and not on prose"` and
`it "control: the scan can see the files it claims to scan"`.

---

## 5. Worked example — the smallest honest UI spec

This uses only APIs verified to exist in the tree: `describe`/`it`/`expect` from
`src/lib/nogc_sync_mut/spec.spl`, and `ui_native_i64_text` from
`src/lib/common/ui/native_scalar_text.spl`. It is a trimmed form of the real
`test/01_unit/lib/common/ui/native_scalar_text_spec.spl`.

```simple
# @cover src/lib/common/ui/native_scalar_text.spl 100%

use std.spec.*
use common.ui.native_scalar_text.{ui_native_i64_text}

describe "runtime-independent UI scalar text":
    it "renders zero, positive, and negative values without runtime externs":
        expect(ui_native_i64_text(0)).to_equal("0")
        expect(ui_native_i64_text(24)).to_equal("24")
        expect(ui_native_i64_text(-1700)).to_equal("-1700")
```

Why this is the shape to copy:

- **No display, no session, no MCP** — it runs anywhere the interpreter runs.
- **Absolute expected values per case** (§4.5), not relative comparisons.
- **No class-element binding**, so §4.1 cannot bite.
- `# @cover` declares what it covers, matching the convention of sibling specs
  under `test/01_unit/lib/common/ui/`.

Run it, and read the bottom line:

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
bin/simple test test/01_unit/lib/common/ui/native_scalar_text_spec.spl > /tmp/out.txt; rc=$?
tail -20 /tmp/out.txt        # must contain `Results: N total, ...`
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
```

No `Results:` line ⇒ inconclusive, whatever `rc` says.

**A live-window example is deliberately not given here.** Writing one would
require asserting that `UITestClient.connect(host, port)` succeeds against a
running harness, and §3 establishes that no display setup exists in this tree —
the honest statement is that the API exists at `client.spl:57` and that whether
it connects in this environment is **undetermined**, not that a template works.

---

## What could not be determined without a GUI

- Whether any `play_sdl2_*` / `play_wm_*` / `play_ui_*` tool connects
  successfully in this environment.
- Whether the 4 `.ppm` goldens currently match compositor output, and whether
  they were ever human-reviewed (no provenance note exists beside them).
- Whether the QEMU GTK capture lane boots here.
- Whether `UITestClient.connect` reaches a harness — the API is verified to
  exist; its runtime behaviour here is untested.

## See also

- `.claude/rules/testing.md` — the authoritative testing rules (`Results:` line,
  matcher list, run-vs-test engine divergence).
- `doc/07_guide/infra/sspec_antipatterns.md`, `doc/07_guide/infra/sspec_typed_evidence.md`.
- `doc/07_guide/ui/ui_stack_guide.md` — what the UI layers are, before you pick one to test.
- `scratchpad/sessions/ui_test_infra_assessment.md` — the inventory this guide's
  §2/§3 numbers come from.

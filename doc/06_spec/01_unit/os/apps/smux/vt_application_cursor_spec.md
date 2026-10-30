# Live VT application cursor mode

**Evidence: AUTHORED / NOT_RUN.** This is a manually maintained source mirror,
not SPipe-generated or executed evidence. Ten scenarios call the production VT
parser and canonical mode accessor. Compilation, case execution, generator
zero-stub admission and SSpec-maintain remain blocked/deferred by the parent
session's source-only restriction. No native input or SendKeys claim is made.

**Executable:** [vt_application_cursor_spec.spl](../../../../../../test/01_unit/os/apps/smux/vt_application_cursor_spec.spl).
**Requirement:** [REQ-CMUX-003](../../../../../02_requirements/feature/caret_mux_tui.md).
**Test plan:** [smux_vt_application_cursor_2026_10_26.md](../../../../../03_plan/sys_test/smux_vt_application_cursor_2026_10_26.md).

## Read and change the live input mode

1. Create a terminal and query private mode one. The expected mode is reset and
   the expected reply bytes are `27 91 63 49 59 50 36 121` (`ESC[?1;2$y`).
2. Split `ESC[?1h` across individual characters. Until the final `h`, the mode
   remains reset. Complete it and expect the mode set without changing content.
3. Split the reset sequence before `l`. The mode stays set until `l` arrives,
   then resets. Visible text remains `visible`; neither transition dirties it.
4. Split `ESC[?1$p` before `p`. No reply exists before the terminator. A set mode
   answers `ESC[?1;1$y`; a subsequent reset/query appends `ESC[?1;2$y` in order.

## Keep input live during a synchronized visual update

1. Print `old`, enter synchronized output, then overwrite the live cells with
   `new`. Set application-cursor mode and query it.
2. Expect the capture to remain `old`, the live mode to be set, and the reply to
   report set. The unpublished update must leave `capture_dirty` false.
3. Reset/query the input mode before publishing. The capture remains `old`,
   while the accessor and reply both immediately report reset.
4. Release synchronization. Expect `new`, reset input mode, and a dirty visual
   publication. An otherwise unchanged frame with only mode changes stays clean.

<details>
<summary>Reset, isolation and preservation cases</summary>

- Ordinary `CSI 1 h/l` and unknown private modes must not mutate DECCKM. Unknown
  mode 9999 still reports `ESC[?9999;0$y`.
- RIS resets the application mode. Resetting an otherwise blank terminal does
  not create a visual-content update.
- Resetting a derived screen leaves the original's set mode intact. Clearing
  pending replies also preserves mode and the original screen's reply bytes.
- Growing and shrinking a screen retain its set mode and text; resizing after
  resetting retains the reset state.
- Each alternate-screen form (47, 1047, 1049) retains the set mode on entry.
  Resetting it there remains effective when primary text is restored.
- Mode-only synchronized publication keeps visual content clean. Resizing during
  a later synchronized update retains the current application mode.

</details>

## Scope and evidence limits

This parser state is a dependency for a future named-key encoder. It does not
implement key encoding, key delivery, terminal negotiation beyond private mode
one, or backend capability discovery. Existing capture/history and historical
VT-v2 evidence retain their original identities. No screenshots or TUI capture
artifacts were produced; all listed expectations remain unexecuted.

<details>
<summary>Executable SSpec source — authored NOT_RUN</summary>

```simple
"""
## Purpose and audience
Maintain the live DECCKM mode used by a future named-key encoder. These cases
exercise the production VT parser and canonical accessor without a host PTY.
## Evidence status
Authored NOT_RUN. Compilation, case execution, SPipe generation and native
compatibility remain unverified. This is not SendKeys or tmux compatibility proof.
## Compatibility and limitations
Mode changes and queries do not change visual capture content. Synchronized
output freezes visuals but never freezes the current child input mode.
"""
# codex-system-test
# @req REQ-CMUX-003
# @manual_section: smux-vt-application-cursor
use std.spec.{describe, it, expect, step}
use std.common.text_bytes.{text_to_bytes}
use os.apps.smux.vt_screen.{vt_new, vt_feed, vt_resize, vt_text,
    vt_replies, vt_clear_replies, vt_application_cursor, vt_alt_screen}

describe "Live VT application cursor mode":
    it "should start reset and report exact reset reply bytes":
        step("Create a terminal and query private mode one")
        var screen = vt_new(2, 12)
        expect(vt_application_cursor(screen)).to_equal(false)
        screen = vt_feed(screen, "\x1b[?1$p")
        expect(text_to_bytes(vt_replies(screen))).to_equal([27u8, 91u8, 63u8, 49u8, 59u8, 50u8, 36u8, 121u8])
        expect(screen.capture_dirty).to_equal(false)
        expect(vt_text(screen)).to_equal("")

    it "should wait for fragmented set and reset terminators":
        step("Split the set sequence at every character boundary")
        var screen = vt_feed(vt_new(2, 12), "visible")
        for fragment in ["\x1b", "[", "?", "1"]:
            screen = vt_feed(screen, fragment)
            expect(vt_application_cursor(screen)).to_equal(false)
            expect(screen.capture_dirty).to_equal(false)
        screen = vt_feed(screen, "h")
        expect(vt_application_cursor(screen)).to_equal(true)
        expect(screen.capture_dirty).to_equal(false)
        step("Split the reset sequence before its terminator")
        screen = vt_feed(screen, "\x1b[?1")
        expect(vt_application_cursor(screen)).to_equal(true)
        screen = vt_feed(screen, "l")
        expect(vt_application_cursor(screen)).to_equal(false)
        expect(screen.capture_dirty).to_equal(false)
        expect(vt_text(screen)).to_equal("visible")

    it "should answer fragmented queries with current set and reset state":
        step("Set private mode one and feed an incomplete DECRQM query")
        var screen = vt_feed(vt_new(2, 12), "\x1b[?1h\x1b[?1$")
        expect(vt_replies(screen)).to_equal("")
        screen = vt_feed(screen, "p")
        expect(text_to_bytes(vt_replies(screen))).to_equal([27u8, 91u8, 63u8, 49u8, 59u8, 49u8, 36u8, 121u8])
        step("Reset the mode and retain ordered replies until drained")
        screen = vt_feed(screen, "\x1b[?1l\x1b[?1$p")
        expect(vt_replies(screen)).to_equal("\x1b[?1;1$y\x1b[?1;2$y")
        expect(vt_application_cursor(screen)).to_equal(false)
        expect(screen.capture_dirty).to_equal(false)

    it "should ignore nonprivate and unknown mode changes":
        step("Send ordinary mode one and an unknown private mode")
        var screen = vt_feed(vt_new(2, 12), "\x1b[1h\x1b[?9999h\x1b[?9999$p")
        expect(vt_application_cursor(screen)).to_equal(false)
        expect(vt_replies(screen)).to_equal("\x1b[?9999;0$y")
        step("Keep a set application mode through unrelated resets")
        screen = vt_feed(screen, "\x1b[?1h\x1b[1l\x1b[?9999l")
        expect(vt_application_cursor(screen)).to_equal(true)
        expect(screen.capture_dirty).to_equal(false)
        expect(vt_text(screen)).to_equal("")

    it "should reset application mode through RIS without inventing visual dirtiness":
        step("Set the mode on an empty terminal and reset the terminal")
        var screen = vt_feed(vt_new(2, 12), "\x1b[?1h")
        expect(vt_application_cursor(screen)).to_equal(true)
        screen = vt_feed(screen, "\x1bc")
        expect(vt_application_cursor(screen)).to_equal(false)
        expect(screen.capture_dirty).to_equal(false)
        screen = vt_feed(screen, "\x1b[?1$p")
        expect(vt_replies(screen)).to_equal("\x1b[?1;2$y")

    it "should preserve copied mode values and mode state while clearing replies":
        step("Copy a set mode and reset only the derived screen")
        val original = vt_feed(vt_new(2, 12), "\x1b[?1h\x1b[?1$p")
        val reset = vt_feed(original, "\x1b[?1l")
        expect(vt_application_cursor(reset)).to_equal(false)
        expect(vt_application_cursor(original)).to_equal(true)
        step("Clear pending replies without changing the live mode")
        val cleared = vt_clear_replies(original)
        expect(vt_replies(cleared)).to_equal("")
        expect(vt_application_cursor(cleared)).to_equal(true)
        expect(vt_replies(original)).to_equal("\x1b[?1;1$y")

    it "should preserve both set and reset state across resize":
        step("Grow and shrink a screen with application cursor enabled")
        var screen = vt_feed(vt_new(2, 12), "value\x1b[?1h")
        screen = vt_resize(screen, 3, 16)
        expect(vt_application_cursor(screen)).to_equal(true)
        expect(vt_text(screen)).to_equal("value")
        screen = vt_resize(screen, 1, 8)
        expect(vt_application_cursor(screen)).to_equal(true)
        expect(vt_text(screen)).to_equal("value")
        step("Reset the mode before the next resize")
        screen = vt_feed(screen, "\x1b[?1l")
        screen = vt_resize(screen, 2, 12)
        expect(vt_application_cursor(screen)).to_equal(false)

    it "should keep one live mode across every supported alternate screen form":
        for mode in [47, 1047, 1049]:
            step("Enter an alternate screen with application cursor enabled")
            var screen = vt_feed(vt_new(2, 12), "main\x1b[?1h")
            screen = vt_feed(screen, "\x1b[?" + mode.to_text() + "h")
            expect(vt_alt_screen(screen)).to_equal(true)
            expect(vt_application_cursor(screen)).to_equal(true)
            step("Reset inside the alternate screen then restore primary content")
            screen = vt_feed(screen, "\x1b[?1l")
            screen = vt_feed(screen, "\x1b[?" + mode.to_text() + "l")
            expect(vt_alt_screen(screen)).to_equal(false)
            expect(vt_application_cursor(screen)).to_equal(false)
            expect(vt_text(screen)).to_equal("main")

    it "should expose live input mode and replies while synchronized visuals stay frozen":
        step("Freeze a visible frame then set the input mode during an update")
        var screen = vt_feed(vt_new(2, 12), "old")
        screen = vt_feed(screen, "\x1b[?2026h\rnew\x1b[?1h\x1b[?1$p")
        expect(vt_text(screen)).to_equal("old")
        expect(vt_application_cursor(screen)).to_equal(true)
        expect(vt_replies(screen)).to_equal("\x1b[?1;1$y")
        expect(screen.capture_dirty).to_equal(false)
        step("Reset live mode before releasing the updated visual frame")
        screen = vt_feed(vt_clear_replies(screen), "\x1b[?1l\x1b[?1$p")
        expect(vt_application_cursor(screen)).to_equal(false)
        expect(vt_text(screen)).to_equal("old")
        expect(vt_replies(screen)).to_equal("\x1b[?1;2$y")
        expect(screen.capture_dirty).to_equal(false)
        screen = vt_feed(screen, "\x1b[?2026l")
        expect(vt_application_cursor(screen)).to_equal(false)
        expect(vt_text(screen)).to_equal("new")
        expect(screen.capture_dirty).to_equal(true)

    it "should keep synchronized mode-only publication visually clean":
        step("Change input mode while holding an otherwise unchanged frame")
        var screen = vt_feed(vt_new(2, 12), "same")
        screen = vt_feed(screen, "\x1b[?2026h\x1b[?1h\x1b[?2026l")
        expect(vt_application_cursor(screen)).to_equal(true)
        expect(vt_text(screen)).to_equal("same")
        expect(screen.capture_dirty).to_equal(false)
        step("Resize during a second synchronization without losing the live mode")
        screen = vt_feed(screen, "\x1b[?2026h")
        screen = vt_resize(screen, 3, 16)
        expect(vt_application_cursor(screen)).to_equal(true)
        expect(vt_text(screen)).to_equal("same")

```

</details>

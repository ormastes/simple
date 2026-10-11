# TUI-web Unicode conversion regression

Source: `test/01_unit/app/ui/tui_web_unicode_spec.spl`.
Owner: `src/app/ui.tui_web/screen_to_html.spl`.
Requirement: REQ-SSPEC-SYSTEM — convert Unicode terminal text without
mixing UTF-8 byte bounds with codepoint-indexed access; retain HTML escaping
and ANSI styling behavior.

Status: **Phase1 seed diagnostics PASS, 4/4**. Evidence:
`build/phase-one-ui-diagnostic/tui_web_unicode_spec/cycle-one.log`; producer and
source identities: `build/phase-one-ui-diagnostic/unicode-repair-inputs.json`.
Native qualification, measured coverage, and docgen remain unverified.
Coverage annotations are targets.

1. Convert the original failing single box corner `┌`; require the complete
   terminal HTML wrapper and exact character.
2. Convert Hangul, an emoji, a combining character, box drawing and `<&>"`;
   require unchanged Unicode and exactly one layer of HTML escaping.
3. Convert cursor positioning and red/reset SGR around Unicode; require the
   exact span boundary, preserved newline and escaped text, and no ANSI bytes.
4. Convert empty text, Unicode with a trailing ESC, and an incomplete CSI;
   require the exact preserved visible content with no indexing failure.

The oracle is complete output equality against explicit expected HTML.
No browser process or screenshot is involved. The implementation splits text
into characters before indexed ANSI lookahead and iterates characters during
escaping, following the existing Screen character-iteration convention.

<details>
<summary>Executable SSpec</summary>

```simple
# codex-system-test
# @tag: unit, ui, tui-web, unicode
# @cover src/app/ui.tui_web/screen_to_html.spl 80%
# Coverage target only; actual execution is recorded separately.
# @req REQ-SSPEC-SYSTEM

use std.spec.{describe, it, expect, step}
use app.ui.tui_web.screen_to_html.{screen_to_html}

# @inline
fn expected_terminal_html(body: text) -> text:
    "<pre class=\"tui-screen\" style=\"font-family:monospace;background:#1e1e1e;color:#d4d4d4;padding:8px;margin:0;line-height:1.2;\">" + body + "</pre>"

describe "TUI-web Unicode HTML conversion":
    it "should preserve a single multibyte box corner without indexing past it":
        step("Convert the box corner that failed in the shared fixture")
        val html = screen_to_html("┌")
        expect(html).to_equal(expected_terminal_html("┌"))

    it "should preserve mixed Unicode and escape HTML metacharacters exactly once":
        step("Convert Unicode text containing HTML metacharacters")
        val html = screen_to_html("┌한글🙂e\u{0301}<&>\"┐")
        expect(html).to_equal(expected_terminal_html("┌한글🙂e\u{0301}&lt;&amp;&gt;&quot;┐"))

    it "should keep ANSI styling aligned across multibyte characters":
        step("Convert styled Unicode surrounded by cursor and reset controls")
        val html = screen_to_html("\u{001b}[2;3H\u{001b}[31m한┌\u{001b}[0m🙂\n<&>")
        expect(html).to_equal(expected_terminal_html("<span style=\"color:#cd0000\">한┌</span>🙂\n&lt;&amp;&gt;"))
        expect(html.contains("\u{001b}")).to_equal(false)

    it "should handle empty input and a trailing incomplete escape after Unicode":
        step("Convert the empty and truncated terminal boundaries")
        expect(screen_to_html("")).to_equal(expected_terminal_html(""))
        expect(screen_to_html("界\u{001b}")).to_equal(expected_terminal_html("界"))
        expect(screen_to_html("界\u{001b}[")).to_equal(expected_terminal_html("界"))
```

</details>

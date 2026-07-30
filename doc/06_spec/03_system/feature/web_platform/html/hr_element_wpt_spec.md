# HTML `<hr>` Canonical Rendering

> This executable scenario promotes one historically partial HTML row: `hr`. It proves the void element survives the canonical HTML semantic tree, receives the selected user-agent separator defaults, accepts author CSS overrides, and renders through `DrawIrComposition -> Engine2D`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HTML `<hr>` Canonical Rendering

This executable scenario promotes one historically partial HTML row: `hr`. It proves the void element survives the canonical HTML semantic tree, receives the selected user-agent separator defaults, accepts author CSS overrides, and renders through `DrawIrComposition -> Engine2D`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md |
| Plan | doc/03_plan/sys_test/html_css_spec_traceability.md |
| Design | doc/05_design/simple_web_browser_engine_production_hardening.md |
| Research | doc/01_research/local/simple_web_browser_engine_production_hardening.md |
| Source | `test/03_system/feature/web_platform/html/hr_element_wpt_spec.spl` |
| Updated | 2026-07-30 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This executable scenario promotes one historically partial HTML row: `hr`.
It proves the void element survives the canonical HTML semantic tree, receives
the selected user-agent separator defaults, accepts author CSS overrides, and
renders through `DrawIrComposition -> Engine2D`.

## Selected profile

The bounded user-agent profile is `display:block`, 8 px block margins, and a
1 px gray border on each side. Author CSS remains later in the cascade and can
replace those defaults with a 32 by 4 px borderless red separator.

The semantic and default-style checks are separate from the authored-CSS checks
so a colored rectangle cannot hide an `hr` parsing or UA-default failure.
Pixel assertions count the exact component rectangle and reject the same color
outside it.

## Evidence boundary

This is source/spec/manual evidence for one deterministic profile. It does not
claim full HTML conformance or qualified execution until a source-admitted
pure-Simple runner executes it. No Rust seed, private painter, GUI fallback,
or alternate cache participates.

**Plan:** doc/03_plan/sys_test/html_css_spec_traceability.md

**Agent plan:** doc/03_plan/agent_tasks/html_css_spec_traceability.md

**Requirements:** doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md

**Design:** doc/05_design/simple_web_browser_engine_production_hardening.md

**Research:** doc/01_research/local/simple_web_browser_engine_production_hardening.md

## Syntax

Run this scenario with a source-admitted pure-Simple test runner:

```sh
<qualified-simple> test test/03_system/feature/web_platform/html/hr_element_wpt_spec.spl --mode=interpreter
```

The placeholder deliberately prevents a stale or Rust-seed binary from being
mistaken for qualified evidence.

## Examples

The control `<hr id='rule'>` resolves to `[0,8,64,2]` with 1 px gray borders.
The authored `#rule` override resolves to `[0,0,32,4]`, removes every border
and margin, and paints exactly 128 red component pixels.

## Requirement traceability

- `REQ-WEB-BROWSER-002` requires the tokenizer/tree path to retain `hr` as a
  childless void element under its authored parent.
- `REQ-WEB-BROWSER-003` requires the selected UA defaults and later author CSS
  to resolve in the canonical style owner.
- `REQ-WEB-BROWSER-004` requires the same semantic/style/layout result to emit
  `DrawIrComposition` and reach Engine2D.
- `REQ-WEB-BROWSER-019` binds the dated corpus row and SHA-256 negative control.
- `REQ-WEB-BROWSER-021` requires this executable SSpec and mirrored manual.

## Canonical path

The HTML tree builder recognizes `hr` as a void element. The web layout
renderer converts it to one `HNode`, applies `tag_defaults`, then applies
presentational, stylesheet, and inline declarations afterward.

The selected default is intentionally implemented in `tag_defaults`; it is not
injected by the test fixture. The author fixture uses normal CSS declarations,
so its zero border and margin prove the cascade can replace the UA values.
The same authored-CSS step also proves exact `border:0px`, `border:none`, and
`border:hidden` clear the default. Mixed digit-bearing invalid values and a
missing declaration preserve it.

Layout consumes the resulting side widths and produces one stable `rule`
component box. DrawIR carries that box, semantic parent, tag style, background,
and border properties. Engine2D consumes the exact composition; this scenario
does not reconstruct geometry or paint into a private framebuffer.

## Expected observations

For the control:

- tag is `hr`;
- parent stable ID is `body`;
- no semantic child exists;
- display is `block`;
- top and bottom margins are 8 px;
- all four borders are 1 px gray;
- DrawIR box is `[0,8,64,2]`;
- Engine2D paints 128 gray pixels inside and none outside.

For the authored override:

- margins are zero;
- border widths are zero;
- exact `border:0px`, `border:none`, and `border:hidden` also clear every
  default border;
- mixed digit-bearing invalid and missing declarations preserve every default
  border;
- DrawIR box is `[0,0,32,4]`;
- command background is `0xFFEF4444`;
- Engine2D paints 128 red pixels inside and none outside;
- the complete pixel buffer differs from the control.

## Failure interpretation

A missing node or child content is a tokenizer/tree failure. A wrong default
margin or border is a UA-style failure. Defaults surviving `border:0` or
`margin:0` are a cascade-order failure. Wrong command geometry is a layout or
DrawIR lowering failure. Correct commands with wrong exact-color counts are an
Engine2D failure. A corpus hash mismatch requires review rather than repinning.

## Review checklist

1. Confirm the executable source contains exactly four visible `step(...)`
   calls and only built-in matchers.
2. Confirm the generated manual mirrors this source and reports zero stubs.
3. Confirm no executable `.spl` file exists under `doc/06_spec`.
4. Record qualified runner path and hash before claiming execution.
5. Keep the other partial HTML rows and animation lane open.

## Scenarios

### HTML hr canonical rendering

#### should render hr defaults and author CSS through Engine2D

- Retain hr as one void Web semantic node
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: sha256_text(HR_CORPUS_ROW) equals `HR_CORPUS_SHA256`
   - Expected: forged_hash == HR_CORPUS_SHA256 is false
   - Expected: defaults.hit_index.nodes[rule_index].tag equals `hr`
   - Expected: defaults.hit_index.nodes[body_index].id_attr equals `body`
- Apply selected hr defaults through WebIR and Draw IR
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 5 expected checks
   - Expected: rule_style.display equals `block`
   - Expected: rule_style.margin_t equals `8`
   - Expected: rule_style.margin_b equals `8`
   - Expected: rule_command.parent_id equals `body`
   - Expected: _hr_style(rule_command, "tag") equals `hr`
- Apply authored CSS through the same WebIR and Draw IR
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 3 expected checks
   - Expected: authored_style.margin_t equals `0`
   - Expected: authored_style.margin_b equals `0`
   - Expected: authored_command.color equals `0xFFEF4444u32`
- "<style>html,body{margin:0}#rule{border:0 url
   - GUI capture: after_step (HTML preferred when available)
- Render discriminating hr pixels through Engine2D
   - GUI capture: after_step (HTML preferred when available)
   - Evidence: GUI state or HTML text verified by 4 expected checks
   - Expected: control.source_kind equals `html_ast`
   - Expected: styled.source_kind equals `html_ast`
   - Expected: control.skipped equals `0`
   - Expected: styled.skipped equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 150 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Retain hr as one void Web semantic node")
expect(sha256_text(HR_CORPUS_ROW)).to_equal(HR_CORPUS_SHA256)
val forged_hash = sha256_text(HR_CORPUS_ROW + "|forged")
expect(forged_hash == HR_CORPUS_SHA256).to_equal(false)
val default_html = (
    "<style>html,body{margin:0}</style>" +
    "<body id='body'><hr id='rule'>after</body>"
)
val defaults = simple_web_layout_render_html_draw_ir_result(
    default_html, HR_WIDTH, HR_HEIGHT
)
val rule_index = _hr_node_index(defaults, "rule")
val body_index = defaults.hit_index.nodes[rule_index].parent.to_i32()
expect(body_index).to_be_greater_than(-1)
expect(defaults.hit_index.nodes[rule_index].tag).to_equal("hr")
expect(defaults.hit_index.nodes[body_index].id_attr).to_equal("body")
expect(
    defaults.hit_index.child_index.child_count[rule_index]
).to_equal(0)

step("Apply selected hr defaults through WebIR and Draw IR")
val rule_style = defaults.hit_index.styles[rule_index]
val rule_command = _hr_command(defaults, "rule")
expect(rule_style.display).to_equal("block")
expect(rule_style.margin_t).to_equal(8)
expect(rule_style.margin_b).to_equal(8)
expect([
    rule_style.border_l, rule_style.border_t,
    rule_style.border_r, rule_style.border_b
]).to_equal([1, 1, 1, 1])
expect(rule_command.parent_id).to_equal("body")
expect(_hr_style(rule_command, "tag")).to_equal("hr")
expect([
    rule_command.x, rule_command.y,
    rule_command.width, rule_command.height
]).to_equal([0, 8, HR_WIDTH, 2])

step("Apply authored CSS through the same WebIR and Draw IR")
val authored = simple_web_layout_render_html_draw_ir_result(
    HR_AUTHORED_HTML, HR_WIDTH, HR_HEIGHT
)
val authored_index = _hr_node_index(authored, "rule")
val authored_style = authored.hit_index.styles[authored_index]
val authored_command = _hr_command(authored, "rule")
expect(authored_style.margin_t).to_equal(0)
expect(authored_style.margin_b).to_equal(0)
expect([
    authored_style.border_l, authored_style.border_t,
    authored_style.border_r, authored_style.border_b
]).to_equal([0, 0, 0, 0])
expect([
    authored_command.x, authored_command.y,
    authored_command.width, authored_command.height
]).to_equal([0, 0, 32, 4])
expect(authored_command.color).to_equal(0xFFEF4444u32)
val none = simple_web_layout_render_html_draw_ir_result(
    "<style>html,body{margin:0}#rule{border:none}</style>" +
    "<body><hr id='rule'></body>",
    HR_WIDTH, HR_HEIGHT
)
val none_index = _hr_node_index(none, "rule")
expect([
    none.hit_index.styles[none_index].border_l,
    none.hit_index.styles[none_index].border_t,
    none.hit_index.styles[none_index].border_r,
    none.hit_index.styles[none_index].border_b
]).to_equal([0, 0, 0, 0])
val zero_px = simple_web_layout_render_html_draw_ir_result(
    "<style>html,body{margin:0}#rule{border:0px}</style>" +
    "<body><hr id='rule'></body>",
    HR_WIDTH, HR_HEIGHT
)
val zero_px_index = _hr_node_index(zero_px, "rule")
expect([
    zero_px.hit_index.styles[zero_px_index].border_l,
    zero_px.hit_index.styles[zero_px_index].border_t,
    zero_px.hit_index.styles[zero_px_index].border_r,
    zero_px.hit_index.styles[zero_px_index].border_b
]).to_equal([0, 0, 0, 0])
val hidden = simple_web_layout_render_html_draw_ir_result(
    "<style>html,body{margin:0}#rule{border:hidden}</style>" +
    "<body><hr id='rule'></body>",
    HR_WIDTH, HR_HEIGHT
)
val hidden_index = _hr_node_index(hidden, "rule")
expect([
    hidden.hit_index.styles[hidden_index].border_l,
    hidden.hit_index.styles[hidden_index].border_t,
    hidden.hit_index.styles[hidden_index].border_r,
    hidden.hit_index.styles[hidden_index].border_b
]).to_equal([0, 0, 0, 0])
val invalid_digit = simple_web_layout_render_html_draw_ir_result(
    "<style>html,body{margin:0}#rule{border:0 1bogus}</style>" +
    "<body><hr id='rule'></body>",
    HR_WIDTH, HR_HEIGHT
)
val invalid_digit_index = _hr_node_index(invalid_digit, "rule")
expect([
    invalid_digit.hit_index.styles[invalid_digit_index].border_l,
    invalid_digit.hit_index.styles[invalid_digit_index].border_t,
    invalid_digit.hit_index.styles[invalid_digit_index].border_r,
    invalid_digit.hit_index.styles[invalid_digit_index].border_b
]).to_equal([1, 1, 1, 1])
val invalid_url = simple_web_layout_render_html_draw_ir_result(
    "<style>html,body{margin:0}#rule{border:0 url(1)}</style>" +
    "<body><hr id='rule'></body>",
    HR_WIDTH, HR_HEIGHT
)
val invalid_url_index = _hr_node_index(invalid_url, "rule")
expect([
    invalid_url.hit_index.styles[invalid_url_index].border_l,
    invalid_url.hit_index.styles[invalid_url_index].border_t,
    invalid_url.hit_index.styles[invalid_url_index].border_r,
    invalid_url.hit_index.styles[invalid_url_index].border_b
]).to_equal([1, 1, 1, 1])
val missing = simple_web_layout_render_html_draw_ir_result(
    "<style>html,body{margin:0}</style>" +
    "<body><hr id='rule'></body>",
    HR_WIDTH, HR_HEIGHT
)
val missing_index = _hr_node_index(missing, "rule")
expect([
    missing.hit_index.styles[missing_index].border_l,
    missing.hit_index.styles[missing_index].border_t,
    missing.hit_index.styles[missing_index].border_r,
    missing.hit_index.styles[missing_index].border_b
]).to_equal([1, 1, 1, 1])

step("Render discriminating hr pixels through Engine2D")
val control = _hr_render(defaults)
val styled = _hr_render(authored)
expect(control.source_kind).to_equal("html_ast")
expect(styled.source_kind).to_equal("html_ast")
expect(control.skipped).to_equal(0)
expect(styled.skipped).to_equal(0)
expect(_hr_color_count(
    control, 0xFF808080u32, true
)).to_equal(HR_WIDTH * 2)
expect(_hr_color_count(
    control, 0xFF808080u32, false
)).to_equal(0)
expect(_hr_color_count(
    styled, 0xFFEF4444u32, true
)).to_equal(32 * 4)
expect(_hr_color_count(
    styled, 0xFFEF4444u32, false
)).to_equal(0)
expect(_hr_pixels_equal(
    control.pixels, styled.pixels
)).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`
- **Plan:** `doc/03_plan/sys_test/html_css_spec_traceability.md`
- **Design:** `doc/05_design/simple_web_browser_engine_production_hardening.md`
- **Research:** `doc/01_research/local/simple_web_browser_engine_production_hardening.md`


</details>

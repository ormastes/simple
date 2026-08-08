# Fieldset and Legend Rendering

Status: **DRAFT / EVIDENCE-BLOCKED**

This is a handwritten mirror of the executable scenario. No admitted
pure-Simple docgen has generated or validated it, so it is not current
generated evidence.

## Purpose

This executable manual verifies the selected deterministic `fieldset` and
`legend` profile from HTML semantics through Web layout, Draw IR, and Engine2D.
It covers `REQ-WEB-BROWSER-002`, `003`, `004`, and `021`.

The implementation uses the canonical renderer and compositor. It does not use
a private painter, GUI-only path, font cache, or bootstrap runtime.

## Supported profile

| Element | Selected user-agent behavior |
|---|---|
| `fieldset` | block; 2 px inline margins; 6/12/10/12 px padding; 2 px solid `#767676` border |
| `legend` | generic inline-block shrink-to-content fallback; 2 px inline padding |

The solid border is the deterministic fallback for a platform-themed groove.
Legend border cutout, its special formatting context, and disabled-form
propagation remain Partial/RED outside this bounded profile.

## Scenario

### Trace selected fieldset and legend semantics to exact pixels

The authored fixture contains a styled fieldset at `[4,4,40,24]` and its
legend at `[10,10,16,8]`. A separate unstyled control uses only the selected
user-agent profile: fieldset `[2,0,92,36]`, legend `[16,8,9,16]`.

1. **Parse fieldset and legend as a semantic parent-child pair**

   The semantic tree must retain `body > fieldset > legend`, with matching
   node and parent identities.

2. **Apply selected user-agent defaults before authored CSS**

   A separate unstyled fieldset must receive the profile in the table above.
   The legend must receive inline-block display and two-pixel inline padding.
   Authored `border:none` and `border:0` controls must each clear all four
   inherited user-agent border widths in computed style and Draw IR.

3. **Lower authored fieldset and legend boxes to exact Draw IR geometry**

   Web hit-index boxes and Draw IR commands must both equal
   `[4,4,40,24]` and `[10,10,16,8]`. Draw IR computed styles must retain
   the `fieldset` and `legend` tags plus authored border, padding, and display.

4. **Rasterize exact component pixels against an unstyled control**

   - `(4,4)` is the authored `#334155` fieldset border.
   - `(6,6)` is the `#f8fafc` fieldset background.
   - `(24,17)` is the `#fde68a` legend background.
   - `(44,4)` remains white immediately after the authored fieldset.
   - `(2,0)` is the unstyled control's `#767676` user-agent border.
   - `(4,2)` is white inside the unstyled control.
   - `(2,2)` and `(48,2)` are backgrounds, not leaked UA borders, for the
     respective `border:none` and `border:0` controls.

Skipped Draw IR commands and a pixel buffer other than `96 × 48` fail the
scenario.

## Failure interpretation

- Wrong parentage is an HTML tree/semantic failure.
- Wrong default metrics are a user-agent style failure.
- Wrong authored values are a cascade failure.
- Different component boxes are a Web layout or Draw IR lowering failure.
- Correct commands with different discriminating pixels are an Engine2D
  failure.

## Evidence boundary

This draft describes executable assertions but does not claim docgen output or
a qualified run. Runner admission, binary SHA, generated-manual provenance,
and result counts remain owned by the HTML/CSS traceability gate. The scenario
intentionally does not claim full WHATWG fieldset rendering, legend border
interruption/special formatting, native theme parity, form validation, or
disabled-descendant behavior.

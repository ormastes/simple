# Layout renderer selector matcher has no `+` / `~` sibling combinators (2026-11-14)

Status: FIXED 2026-11-14 on `work/webrender-selector-combinators-20261114` — `+` and `~` are tokenised and matched on both the text and pre-parsed paths; the three rows below are asserted in `structural_pseudo_class_chrome_parity_spec.spl`. Original report follows.

Severity was: medium (a rule using them never applies; nothing over-matches).

## Defect

`selector_group_parts` (`simple_web_html_layout_renderer_core_selectors.spl`)
splits a selector group on spaces and treats `>` specially. `+` and `~` become
ordinary parts, are parsed as a type selector named `+` / `~`, and the
right-to-left walk then looks for an ANCESTOR with that tag — so the rule
matches nothing. Written without spaces (`p+div`) the whole text is one
compound with base `p+div`, which also matches nothing.

## Chrome 159.0.8154.6 vs Simple

Fixture: `<section><p id=q1/><div id=q2/></section><section><p id=w1/><div id=w2/><div id=w3/></section>`,
base `* {width:200px}`, probe `SELECTOR {width:50px}`, matched ids by computed width.

| selector | Chrome | Simple |
|---|---|---|
| `p:nth-child(1) + div` | q2 w2 | (none) |
| `p:nth-child(1) ~ div` | q2 w2 w3 | (none) |
| `p:nth-last-child(2) + div` | q2 | (none) |
| `p:nth-last-child(1) + div` | (none) | (none) |

## Why it is not fixed with the An+B follow-up

It needs a previous-element-sibling index in `SelectorContext`, two new part
kinds on both the text and pre-parsed paths, the tokenizer (`p+div`,
`a~b` without spaces, `[attr~=v]` and `:nth-child(2n+1)` must stay intact),
specificity, and `selector_group_ancestor_keys` — its soundness argument
assumes every part left of the subject matches an ancestor, which a sibling
compound does not. Rules that never applied would start applying on the
catalog pages, so the pixel and geometry ratchets need a reviewed update in
the same change.

## Evidence

`test/01_unit/browser_engine/structural_pseudo_class_chrome_parity_spec.spl`
lists the three rows as NOT ASSERTED.

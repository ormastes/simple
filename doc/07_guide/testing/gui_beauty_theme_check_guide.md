# GUI Beauty and Theme Check Guide (Agent Workflow)

Mandatory GUI verification workflow for LLM agents (Kimi, Codex, Claude, Gemini)
working on the Simple UI lanes: **Engine2D (2D)**, **Web (HTML/CSS)**, **GUI
(widgets)**, and **WM (window manager)**.

A GUI change is not done when it renders. It is done when it renders, handles
events, applies the selected theme correctly, and passes a beauty review.

## Two-Stage Pipeline

Run the cheap deterministic gate first, the expensive subjective pass last:

```
Stage 1 (Linux, headless):  functional + event + pixel + theme-token checks
Stage 2 (macOS, native):    final beauty review on real Retina rendering
```

Stage 1 is CI-friendly and reproducible; it must pass before Stage 2 is even
started. Stage 2 exists because some aspects of beauty are only real on native
display hardware (see below).

## What Headless Linux Can and Cannot Verify

**Event handling — fully testable headless.** A display server is not required
to test interaction. Inject synthetic input (X11 XTEST via `xdotool`, or direct
event-queue injection through the app harness used by `app/ui/ui_access.md`)
and assert on resulting state: focus transitions, hit-testing, click/hover/key
routing, scroll behavior, window raise/move/resize for WM. This covers 100% of
event-logic correctness.

**Beauty — objectively testable, subjectively not.** Headless rendering can
verify every *measurable* proxy of beauty:

- Pixel determinism (same input → same pixels) and golden-image diffs
- Theme tokens applied: computed colors, font family/size/weight, spacing,
  corner radius match the selected theme (`config/themes/*.simple-theme`,
  `config/theme/*.css`) — not just "some color was painted"
- Contrast ratios (WCAG AA: 4.5:1 text, 3:1 large text/UI) computed from pixels
- Alignment and spacing consistency: elements on a common grid, uniform
  padding/margins, no 1px jitter between sibling widgets
- No clipped/overlapping text, no unintended scrollbars, no empty regions
  where content should be

What headless Linux **cannot** judge (this is what Stage 2 is for):

- Subpixel antialiasing and font rasterization quality (freetype/Xvfb ≠ macOS
  Core Text / Retina)
- HiDPI/Retina scaling correctness (2x assets, crisp edges at scale factors)
- Native GPU backend output (Metal vs software/X11 rendering)
- Animation smoothness and perceived feel
- The subjective call: does it actually look good, balanced, professional

## Theme/CSS Applied Check (Required)

For every themed surface, verify the *computed* style, not the source:

1. Select theme explicitly (e.g. `obsidian`, `aqua_glass`) — never test with
   implicit defaults.
2. Assert per widget class: background, foreground/text, accent, border color,
   font family/size/weight, padding, corner radius equal the theme tokens.
3. Repeat for both a dark and a light theme; a token that only works in one
   mode is a bug.
4. For the web lane, diff computed CSS against the theme source; catch
   hardcoded hex values in producers that bypass the theme (these belong in
   bug reports, not workarounds).
5. Check theme *switching* at runtime: re-render after a switch, assert all
   surfaces pick up new tokens (stale caches are the common defect).

## Beauty Checklist (Both Stages)

Objective (Stage 1, assert in tests):

- [ ] Text never clipped, ellipsized, or overlapping
- [ ] Sibling elements share alignment edges; spacing is uniform
- [ ] Contrast ratios pass WCAG AA from measured pixels
- [ ] Colors/fonts/spacing match theme tokens exactly
- [ ] Golden-image diff empty or classified FRINGE-only (see
      `ui/pixel_comparison_guide.md`)
- [ ] Empty states, error states, and overflow states render deliberately

Subjective (Stage 2, agent judges from screenshots):

- [ ] Visual hierarchy reads correctly (primary action stands out)
- [ ] Density feels right — neither cramped nor sparse
- [ ] Crisp on Retina: no blurry text or 1px seams
- [ ] Animations/transitions feel smooth and deliberate
- [ ] Dark and light themes both look intentional, not inverted-afterthought

## Per-Lane Improvement Questions

Ask these during every GUI review; file concrete bugs for every "no":

**Engine2D (2D)**
- Is Draw IR minimal — no transient atlas/cache material leaking in?
- Does text go through the canonical `draw_text` / selected-font path?
- Are CPU SIMD and backend render outputs pixel-parity clean
  (`scripts/check/check-production-gui-web-renderer-parity-evidence.shs`)?

**Web (HTML/CSS)**
- Do producers lower through web semantic/layout into `DrawIrComposition`
  (no private parallel draw paths)?
- Does computed CSS match theme tokens in both modes?
- Does Simple rendering stay FRINGE-classified vs the Chromium reference?

**GUI (widgets)**
- Do all states render: normal, hover, pressed, focused, disabled, selected?
- Is focus order keyboard-complete and visible?
- Do pairwise matrix cases stay green (`testing/gui_widget_*` docs)?

**WM (window manager)**
- Decorations, focus ring, stacking order, snap/resize correct under
  `app/ui/wm_compare.md` screenshot diffs?
- Do events route to the right window under overlap/occlusion?
- Theme applied to *frame* surfaces too, not just client content?

## Tooling

| Stage | OS | Tools |
|-------|----|-------|
| Event tests | Linux | `xvfb-run` + `xdotool` (XTEST), or harness event injection (`app/ui/ui_access.md`) |
| Pixel/golden | Linux | `tools/pixel_compare/*`, `wm_compare` harness, `scrot`/`import` |
| Theme tokens | Linux | Computed-style assertions in spec files, CSS diff vs `config/theme(s)` |
| Parity gate | Linux/macOS | `sh scripts/check/check-production-gui-web-renderer-parity-evidence.shs` |
| Beauty pass | macOS | `screencapture` (window/screen), `cliclick` (interaction), `osascript` (window control), Playwright (web lane) |

macOS agent loop: launch app → wait for render → `screencapture -l <windowid>`
→ view PNG → `cliclick` to navigate states → re-capture → judge against the
subjective checklist → file bugs or approve.

## Rules

- Never mark GUI work done on Stage 1 alone — the macOS beauty pass is required.
- Never skip the theme-token check because "it looks right in one theme."
- A failing beauty item is a concrete bug report (what, where, expected vs
  actual, screenshot), not a subjective shrug.
- Headless Linux event tests are mandatory even when the final target is
  macOS-only — event logic bugs are cheaper to catch there.

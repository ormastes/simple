<!-- codex-design -->
# VS Code Rich Editor Line Number Alignment Attempts

**Date:** 2026-04-12  
**Scope:** vertical centering of line numbers beside tall rendered math lines in `src/app/vscode_extension`

## Current Status

Math rendering works.

Line-number alignment is now **deferred** and is not part of the current VS Code extension migration work.

The current editor should be treated as “good enough to ignore gutter alignment for now” unless the migration work later depends on it.

## Tried And Failed

### 1. Direct gutter CSS on `.cm-gutterElement`

Tried:

- flex-based alignment on `.cm-gutterElement`
- table-cell / `vertical-align: middle`
- padding-based approximation

Result:

- one version hid or corrupted the line-number gutter
- the others did not truly center the numbers
- these approaches fight CodeMirror’s managed gutter layout

Do not retry:

- global flex/table hacks on `.cm-gutterElement`
- padding-only “fake centering” as the main solution

### 2. `lineNumberWidgetMarker` on current inline replacement widgets

Tried:

- using CodeMirror’s `lineNumberWidgetMarker`

Result:

- ineffective for the current math render path
- reason: our math rendering uses inline replacement widgets, while the useful widget-marker path is oriented around block widgets

Do not retry:

- `lineNumberWidgetMarker` while math is still rendered as the current inline replacement widget

### 3. Full block-widget math-line rewrite

Tried:

- rewriting rendered math lines into block widgets so `lineNumberWidgetMarker` would apply officially

Result:

- broke math rendering entirely in practice
- reverted

Do not retry immediately:

- another large block-widget rewrite without first isolating a minimal prototype and proving it renders correctly

### 4. Custom gutter replacement attempt

Tried:

- replacing the built-in line-number gutter with a custom gutter
- sizing marker DOM using measured line height

Result:

- numbers rendered again
- centering still not correct in the visible result

Do not retry immediately:

- the exact same custom-gutter implementation

### 5. Focused per-line gutter marker / class strategy

Tried:

- `lineNumberMarkers` plus per-line gutter classes
- marker DOM height sync against measured line blocks

Result:

- rendering stayed stable
- line numbers still did not visually center in an acceptable way

Do not retry immediately:

- the same measured-height marker sync approach on the inline math widget pipeline

## Methods Still Open

### A. Minimal isolated block-widget prototype

Status:

- now implemented narrowly for full-line math blocks
- candidate result only, not yet user-approved

Why this is the current candidate:

- uses CodeMirror’s official block-widget + `lineNumberWidgetMarker` path
- avoids the earlier broad rewrite that broke rendering
- keeps inline rendering for all non-full-line cases

### C. Fully owned custom gutter plus explicit measured layout contract

Status:

- partially tried, not exhausted

Why still possible:

- may still work if the marker DOM and the measured block layout are redesigned together instead of patched incrementally

### D. Monaco inside the webview

Status:

- researched only, not attempted

Why still possible:

- Monaco gives stronger gutter/layout control inside a webview than stock VS Code extension editor APIs
- this is a much larger architecture move

## Recommendation

Do not spend more time on:

- global gutter CSS hacks
- widget-marker APIs on the current inline math widget path
- another broad block-widget rewrite without a minimal prototype
- the focused measured-height marker sync that still left the numbers visibly off-center

If line-number centering remains required, the next serious options are:

1. validate or reject the current minimal block-widget candidate with human visual review
2. if rejected, fall back to top-aligned numbers on the stable inline renderer
3. only after that, consider a redesigned custom gutter or a Monaco-based webview

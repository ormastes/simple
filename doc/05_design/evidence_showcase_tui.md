<!-- codex-design -->
# TUI Design: Evidence Showcase

## Purpose

Keep the showcase and generated manuals useful in a terminal, plain Markdown
viewer, or text-only review.

## Root layout

```text
SIMPLE EVIDENCE SHOWCASE
Generated from receipts at REVISION / DATE

Status summary
LIVE  HISTORICAL  CONTRACT  BLOCKED  UNSUPPORTED  PLANNED

Operating systems and hardware
Capability        Status          Target       Proof / Resume
RISC-V Linux      historical      RV32 QEMU    manual · receipt · rerun
SimpleOS WM       blocked         x86_64 QEMU  latest FAIL · resume
Physical ARM      blocked         unselected   select board profile

Web and database
...
```

Tables remain narrow. Long claim boundaries render beneath the row in a folded
details section when supported, or as an indented paragraph in plain text.

## Generated-manual evidence order

```text
Evidence at a glance
Claim:
Status:
Target:
Revision/freshness:
Receipt:

1. Capture the feature evidence
2. Verify the structured evidence
3. Render the evidence for review
4. Publish the showcase link

[compact text/event/protocol evidence]

Diagnostics / raw artifacts (folded)
Executable SSpec (folded)
```

## Text captures

- Embed a bounded normalized excerpt in a fenced `text` block.
- Link raw and complete normalized transcripts.
- Print whitespace policy and mask names.
- On failure, show expected index, actual line, reason, and nearby lines.

## Motion fallback

Text-only review displays:

```text
duration: 1840 ms
events: 3
keyframes: 3

1  0 ms     focus     editor.body       PASS
2  420 ms   text      editor.body       PASS
3  1800 ms  command   editor.run        PASS
```

Keyframe/media paths remain links. Motion never requires autoplay.

## Accessibility

- Status is literal text, never color-only.
- Every media item has a one-line evidence summary.
- Protocol importance uses text such as `CRITICAL`.
- Motion always has an ordered transcript.

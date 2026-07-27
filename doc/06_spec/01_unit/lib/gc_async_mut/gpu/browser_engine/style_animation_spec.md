# Browser CSS Animation Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 6 | 6 | 0 | 0 |

## Scenarios

- Animation and transition updates retain the target DOM node identity.
- Typed color, length, and numeric keyframe values interpolate.
- Repeated animations start each new iteration at the first keyframe.
- Reversed author keyframes are normalized by offset; one rule retains at most
  256 frames and one stylesheet retains at most 1024 keyframe rules.

Requirement trace: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-017.

Source:
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/style_animation_spec.spl`

Updated: 2026-07-26.

# HTML/CSS Full Rendering Goal Status - flex-flow

Date: 2026-06-27

## Scope

This report records the narrow `flex-flow` Simple Web renderer slice. It does
not claim full CSS completion, RenderDoc `.rdc` completion, Metal completion,
or D3D12 completion.

## Change

- `flex-flow` is listed as implemented Simple Web CSS.
- Existing style parsing expands `flex-flow` into `flex-direction` and
  `flex-wrap`.
- Draw IR computed style now exposes the existing `flex-direction` and
  `flex-wrap` renderer fields.
- Renderer coverage asserts `flex-direction=column` and `flex-wrap=wrap`
  Draw IR style values for a `flex-flow: column wrap` scene.

## Current Evidence

- Implemented CSS: `135/135`
- Full CSS rendered: `135/394`
- Full CSS unrendered: `259`
- Unsupported inventory ownership: `266`

## Remaining Blockers

- Full CSS specification coverage remains incomplete.
- Native RenderDoc `.rdc` capture remains blocked on this host by missing
  RenderDoc command-line tooling.
- Linux Vulkan, macOS Metal, and Windows D3D12 native render-log comparisons
  still require prepared platform hosts and valid native capture artifacts.

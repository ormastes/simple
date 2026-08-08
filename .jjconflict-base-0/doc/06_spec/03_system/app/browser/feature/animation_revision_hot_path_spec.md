# Revision-Driven Animation Advance

> Operator scenario for REQ-WEB-BROWSER-004 and REQ-WEB-BROWSER-006.

| Field | Value |
|---|---|
| Status | Static-ready; runtime execution held pending a source-admitted pure-Simple CLI |
| Executable source | `test/03_system/app/browser/feature/animation_revision_hot_path_spec.spl` |
| Rendering owner | hosted registry → `HostedWebContentSession` → `BrowserSession` → canonical Draw IR → Engine2D |
| Unsupported claims | No RSS threshold, native/GPU receipt, or general browser conformance claim |

## Purpose

The hosted animation clock already receives document, style, and resource
revisions from `BrowserSession`. This scenario proves the frame owner uses
those revisions rather than allocating and scanning
`current_style_html + current_body_html` on every animation tick.

## Operator flow

1. **Open a CSS animation in the hosted BrowserSession**
   - Load one `32x24` element with a linear red-to-blue CSS keyframe.
   - Confirm one reconciled animation instance.
2. **Render the exact initial Draw IR and Engine2D frame**
   - Derive time from the session's monotonic clock.
   - Require one HTML-AST batch and exactly one rectangular `stage` command
     at `0,0,32,24`.
   - Require ARGB `0xFFDC2626` in all 768 pixels with zero skipped commands.
3. **Advance CSS and render the exact midpoint frame**
   - Advance through the production registry; derive 500 ms elapsed time from
     the resulting session state.
   - Again require exactly one rectangular `stage` command.
   - Require ARGB `0xFF804488` in all 768 pixels with zero skipped commands.
4. **Read the published frame through the production registry cache**
   - Call the actual registry `body_html` route.
   - Require the hosted getter to return `published_body_html` directly.

## Expected receipt

```text
initial  0|html_ast|1|1|rect:stage:0,0,32,24:4292617766|0|768
midpoint 500|html_ast|1|1|rect:stage:0,0,32,24:4286596232|0|768
registry body route returns the revision-refreshed published frame
```

## Failure handling

- A pixel or Draw IR mismatch fails the executable SSpec.
- Reintroduction of whole-document concatenation in the production body getter
  fails the cache-route guard.
- Do not substitute the Rust seed or bootstrap solely to run this scenario.

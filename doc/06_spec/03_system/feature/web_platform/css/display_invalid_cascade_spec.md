# CSS invalid display cascade

> Static candidate manual — runtime unclaimed. This hand-reviewed mirror
> records expected oracles from the executable SSpec; it is not generated PASS
> evidence.

Requirements: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
REQ-WEB-BROWSER-021.

## Resolve duplicate display declarations through both style paths

Four absolute 2-by-2 red probes exercise dispatch-only and full-reconstruction
declaration paths. `display:none;display:bogus` must compute to `none` in both
paths. The reverse control `display:bogus;display:block` must compute to
`block` in both paths.

## Keep hidden nodes out of canonical Draw IR

Neither hidden probe has a Draw IR command. The visible controls remain
canonical `rect` commands at `[4,1,2,2]` and `[6,1,2,2]`; no private rendering
path is introduced.

## Render exact visible-control Engine2D pixels

Expected skipped-command count: `0`.

Expected full 8-by-4 framebuffer:

```text
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFEF4444 0xFFEF4444 0xFFEF4444 0xFFEF4444
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFEF4444 0xFFEF4444 0xFFEF4444 0xFFEF4444
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
```

## Claim boundary

This bounded slice covers invalid-value skipping for the renderer's existing
display keyword set. Unsupported display values and CSS-wide keyword semantics
remain outside scope.

## Evidence provenance

No bootstrap was invoked. The expected oracles remain static until qualified
pure-Simple SSpec execution and docgen are available.

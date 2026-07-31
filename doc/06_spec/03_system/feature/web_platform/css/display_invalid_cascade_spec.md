# CSS invalid display cascade

> Static candidate manual — runtime unclaimed. This hand-reviewed mirror
> records expected oracles from the executable SSpec; it is not generated PASS
> evidence.

Requirements: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
REQ-WEB-BROWSER-021.

## Resolve duplicate display declarations through both style paths

Dispatch-only declarations prove that `display:none;display:bogus` retains
`none` and `display:none;display:initial` resolves to the renderer initial
`block`. Full-reconstruction declarations prove malformed-value skipping and
that an important `unset` resolves to `block`. Important `inherit` copies the
parent's computed `inline`; important author-origin `revert` restores the UA
`inline` default for `span`.

## Keep hidden nodes out of canonical Draw IR

Neither hidden probe has a Draw IR command. The visible full-path control
remains a canonical `rect` command at `[6,1,2,2]`; no private rendering path is
introduced.

## Render exact visible-control Engine2D pixels

Expected skipped-command count: `0`.

Expected full 8-by-4 framebuffer:

```text
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFEF4444 0xFFEF4444
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFEF4444 0xFFEF4444
0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF 0xFFFFFFFF
```

## Claim boundary

This bounded slice covers invalid-value skipping, `initial`, `unset`, `inherit`,
and author-origin `revert`. Unsupported display values remain outside scope.
`revert-layer` remains a provenance HOLD because the current parser flattens
`@layer` before cascade resolution.

## Evidence provenance

No bootstrap was invoked. The expected oracles remain static until qualified
pure-Simple SSpec execution and docgen are available.

# CSS invalid display cascade

> Static candidate manual — runtime unclaimed. This hand-reviewed mirror
> records expected oracles from the executable SSpec; it is not generated PASS
> evidence.

Requirements: REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004,
REQ-WEB-BROWSER-021.

## Resolve duplicate display declarations through both style paths

Dispatch-only declarations prove that `display:none;display:bogus` retains
`none` and `display:none;display:initial` resolves to the CSS initial `inline`.
Full-reconstruction declarations prove malformed-value skipping and that an
important `unset` also resolves to `inline`. Important `inherit` copies the
parent's computed `inline`; important author-origin `revert` restores the UA
`inline` default for `span`.

Inside a `display:none` parent, an ordinary `div` and a `display:revert` div
both retain their UA computed `block`; ancestor suppression, not inherited
display poisoning, keeps them invisible. An explicit `display:inherit` child
computes to its parent's `none`. Each child has bounded, distinct background
and text paint material, so command absence cannot pass vacuously.

A lower normal `display:contents` with authored width and margin, followed by
important `display:block`, computes to block while retaining width `3` and
left margin `2`; only the final display winner may apply contents side effects.

## Keep hidden nodes out of canonical Draw IR

Neither hidden probe nor any paint-producing hidden-parent child has a Draw IR
command. The visible full-path control remains a canonical `rect` command at
`[6,1,2,2]`; no private rendering path is introduced.

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

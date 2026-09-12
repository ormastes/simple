# browser_engine: table rows lay cells vertically (no horizontal table layout)

- Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
- Area: `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`
  (`tag_defaults` treats `table`/`tr`/`td`/`th` as plain `display:block`;
  `layout_table.spl` exists but is not wired into this renderer's flow)
- Found: 2026-07-11 (news.ycombinator.com render comparison vs Chrome headless)

## Summary
`<tr>` children stack vertically like block boxes instead of flowing
horizontally as table cells. On Hacker News every story renders as
"rank" on one line, then the title on the next, then the subtext — Chrome puts
rank + title on one row via `<tr><td>1.</td><td>title</td></tr>`. Any
table-based layout (HN, many older sites, HTML email) is structurally wrong.

## Repro (minimal)
```html
<html><body style="margin:0"><table>
  <tr><td>A</td><td>B</td></tr>
</table></body></html>
```
Chrome: `A B` on one line. Simple engine: `A` above `B` (two block lines).
Render via `simple_web_layout_render_html_software_pixels(html, 200, 120)` and
inspect the first two text lines.

## Scope note
This is a missing feature, not a small fix: needs `display:table-row` semantics
(horizontal cell placement, shared row height) and at least auto column sizing.
`table-layout: fixed` + equal-width columns would already fix most of HN's
structure. Filed instead of fixed per session scope (surgical fixes only).

## Related fixed the same day
Presentational attributes (`bgcolor`/`width`/`height`/`align`) now map to
lowest-priority CSS decls, so HN's orange `bgcolor="#ff6600"` header bar and
table widths paint; only the horizontal cell flow remains wrong.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

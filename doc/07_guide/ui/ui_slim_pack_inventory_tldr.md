# UI slim pack inventory — tl;dr

`sh scripts/check/check-ui-slim-pack-inventory.shs --seed <seed> ENTRY.spl...`
classifies each entry's real `deps fast` closure into named packs
(`config/ui/pack_prefixes.sdn`) and checks the result against the
`tui-hello-static` / `gui-hello-static` recipes. It is a report (no pack
loader exists), not a build gate.

Verdict: `PASS — <n> entries inventoried, 0 violations` /
`FAIL — ... violations: <entry:pack,...>` /
`ERROR — nothing was checked (<reason>)`. Prefixes in the config that don't
exist on disk are an ERROR (stale config), not an empty pack.

Real run 2026-09-06 against the plan's entry map: **ERROR — stale pack
prefix(es): layout, widgets, session, draw_ir** — those four directories
don't exist yet. See `doc/07_guide/ui/ui_slim_pack_inventory.md`.

`--selftest` — 4 fixtures, fatal.

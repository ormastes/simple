# Parser: `impl X: Trait` engine-block fails in bootstrap compiler

**Priority:** medium (pre-existing repo issue; not introduced by game2d-framework)
**Filed:** 2026-04-25
**Component:** parser (Rust bootstrap + self-hosted)
**Discovered by:** game2d-framework SStack Phase 5/7 (pre-existing issue surfaced)

## Description

`impl X: Trait` blocks fail to parse in the bootstrap compiler. This is a
pre-existing repo issue, not a regression introduced by the game2d-framework
feature, but it directly blocks the **AC-5 real-demo hash pin** (see
`game2d_real_demo_hash_pin.md`) because programmatic `HeadlessBackend` boot
walks through the `impl HeadlessBackend: GameBackend` block.

Per `git blame`, this predates the `game2d-framework` feature work — the
defect lives in the parser's `impl_block` arm, surfaced by any class that
declares trait conformance via the `impl X: Trait` form (vs. inline
`class X: Trait` in the class header).

## Evidence

- `src/lib/nogc_sync_mut/game2d/backend/headless.spl:212` — `impl HeadlessBackend: GameBackend` block fails to parse via bootstrap binary.
- `src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl` — same shape, same failure.
- `.sstack/game2d-framework/state.md` `### 5b` and `### 7-verify-rerun-2 W4` item 5: "`impl X: Trait` engine-block parse repair — pre-existing repo issue, affects `headless.spl:212`, `sdl_backend.spl`".

## Workaround currently in use

Class-header inline form (`class HeadlessBackend: GameBackend`) parses correctly
and is preferred. The post-class `impl X: Trait` form is reserved for sites
where the trait conformance is added in a separate file from the class
declaration — those sites currently have no other option, hence the live
blockers in headless / sdl backends.

## Suggested fix direction

`git blame` the parser's `impl_block` arm to find the original drift; the
single-line `if cond:` member-target gap (filed
`parser_member_target_in_single_line_if.md`) lives nearby in the same parse
function tree, so a combined repair pass is plausible.

## Related

- `doc/08_tracking/bug/parser_member_target_in_single_line_if.md` (sibling parser gap)
- `doc/08_tracking/bug/game2d_real_demo_hash_pin.md` (downstream consumer)

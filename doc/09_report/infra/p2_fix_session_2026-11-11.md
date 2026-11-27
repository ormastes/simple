# P2 essential-bug fix session (2026-11-10 .. 2026-11-11)

Scope: P2 essential bugs on `release/1.0.0` (compiler, interpreter, seed, lib/rt,
test runner, tests). P3 handled by a separate session. Every fix landed by PR to
`release/1.0.0`; landed fixes are `fix-implemented-verification-pending` (FIV),
never `fixed` — native stage2/stage3/QEMU verification is still owed per shard log.

## Process
- Per-bug shards `doc/08_tracking/bug/db/<id>.sdn` + exactly one
  `.xxh3_<hash>.csm` sidecar (0 bytes; hash is in the name, = `xxhsum -H3` of the
  CR-stripped shard). Legacy `bug_db.sdn` is frozen.
- Lanes: Sonnet implements / Opus (Fable when stuck) plans and reviews; lane opens
  PR and stops at "NEEDS REVIEW"; reviewer merges with `gh pr merge --admin --merge`.
- Env/blocked bugs: fix + strongest interpreter/MIR tests, land FIV naming the
  remaining native check.
- Push env: `MUST_CHECK_PUSH_BUDGET_S=900 MUST_CHECK_REMOTE_QUERY_TIMEOUT_S=120`,
  never `--no-verify`. Push from a worktree that has full `scripts/` + `config/`
  (sparse or old checkouts fail `push-sdn-row-shape` with ERROR).

## Landed (about 85 PRs)
#8187 #8194 #8200 #8203 #8208 #8209 #8213 #8216 #8217 #8219 #8222 #8228 #8230
#8231 #8233-#8238 #8244-#8250 #8252 #8255 #8257 #8258 #8260-#8262 #8290 #8292
#8293 #8295-#8298 #8302-#8305 #8307-#8311 #8314 #8315 #8322 #8324-#8326 #8328
#8329 #8331 #8333-#8337 #8339 #8342 #8344 #8345 #8347-#8352 #8355 #8356 #8358
#8361 and the ponytail hook fix #8350.

## Open PRs at the cut (all required checks were re-run after `update-branch`)
- #8359 compiler sweep residuals (seed `Some(None).?` fix; red->green not yet
  independently shown).
- #8360 prelude `panic` unshadowable (Rust test never ran: build timed out).
- #8362 cranelift phi n-ary slot, #8363 lexer imported-method lookup (pin only).
- #8364 native trait typed-return receiver (required check failing — inspect).
- #8365 JS DOM globals (partial; shard stays open).
- #8354 spec path refs (branch head not resolvable — re-push or close).

## Unlanded work in lane worktrees (C:/dev/wt)
- p2-optprim: seed primitive `T?` as real Option (plan: scratchpad
  parse_family_minimal_plan.md); green run in progress at the cut.
- p2-mcpwhen: MCP startup — add `export`s in `src/app/protocol/*.spl`, `.cmd`
  wrappers emit a JSON-RPC error + stderr tail on failure. Root cause: stale
  Oct-22 seed `target/bootstrap/simple.exe` + private-fn visibility (seed
  6d15331f91e). Needs seed redeploy too.
- lib/rt lane: bug 2 pushed without PR; bug 3 (web style) not done.
- seed lane: bool param / resource decl / `mut` seed half mid-edit.
- blocked-bug lane: stage2join, theme aggregate return, cold-init admission,
  private-names selfhost, text-index char/int flip to error — mid-edit.
- drvv1: driver v1 callable loader (Fable), spec fix in progress.
- Not started: cuda optimizer surface owner, bare-field sweep, 21 of 24 cargo
  test-group tests.

## Known process hazards found
- Two `.csm` sidecars on one shard (reseal without deleting the old one) fails
  the required `local-sdn-crc32-sealed` gate and poisons every PR that later
  merges the base; fix = delete the sidecar whose hash != `xxhsum -H3`.
- `git stash` is shared across worktrees; a lane popped another lane's stash.
- Cleanup agents must not delete active lane worktrees or the session scratchpad.

## Builds
- Stage3: `C:\dev\p3new\stage2new\go_s3b.ps1`, 24 h deadline loop, source
  `C:/dev/wt/p4-compiler` @ 03f360a361a (B5b fix, landed as #8336).
- Phase 4: `C:\dev\p3new\s4new\run_p4.ps1`; binary sanity check still pending.

## P2 remaining at release tip 93ae155618c (before the last merges)
open 71, fixing 5, blocked 5 (FIV and obsolete excluded).

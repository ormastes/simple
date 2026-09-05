# vcs.md overstated pre-push guard wiring; 5 green gates sat at bootstrap tier — 2026-09-01

## Ground truth (origin/main 5e09b3ef2fd)

Chain: `.git/hooks/pre-push` -> `scripts/hooks/pre-push` (dispatcher) ->
`scripts/check/pre-push-conflict-tree-guard.shs` (runs `check-hook-installation.shs`
at :116, then `exec sh check-push-must-pass.shs --from-pre-push-hook` at :135) ->
ledger/manifest validation + conflict-tree union + manifest-declared push-tier gates
(`run_manifest_push_gates`, `check-push-must-pass.shs:282-352`).

The wiring surface is **`config/check/must_check_gates.sdn`** (rows with `tier=push`),
not a hardcoded list inside the dispatcher. `check-push-must-pass.shs:348` has a
fail-closed `*) return 2` arm, so a manifest row with no matching case arm blocks
every push — the manifest and the case-arm table must stay in lockstep.

**The "only five guards run" hypothesis is FALSE.** Before this change 13 push-tier
gates executed (12 blocking, 1 advisory). vcs.md's real defect is different and
narrower: it says several guards are "wired into pre-push-conflict-tree-guard.shs",
which names a surface that no longer executes guards directly, and it claims wiring
for gates that sat at `tier=bootstrap` and therefore executed on no push at all.

## The actual fail-open

Seven guards were declared `tier=bootstrap, push_blocking=false, mode=automated`
with ledger rows permanently `todo, never`. `ledger_is_unpromoted_at_rev` tolerates
TODO rows while `source_fingerprint: "unrecorded"`, so those gates ran nowhere and
nothing complained. Three of them were **green on main** and cost seconds.

`check-guard-wiring.shs` cannot see this: its "reached" set is text reachability, so
a case arm in `check-push-must-pass.shs` counts as wired even when no manifest row
selects it. That is why `check-c-runtime-compiles-push.shs` is absent from
`guard_wiring_unwired_baseline.txt` (751 entries, not 405) while executing on no push.

## Measured verdicts (worktree /mnt/data/gwaudit at origin/main, rc read on the next line)

WIRE-NOW (green, seconds):
- `check-c-runtime-compiles-push.shs` rc=0 — `PASS — 128 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)`
- `check-no-direct-rt.shs --roots src` rc=0 — `PASS — 16209 file(s) scanned (roots=src, src=6475), forbidden=6475, extern_decls=6467 (baseline 7776)`
- `check-guard-wiring.shs` rc=0 — `check-guard-wiring: PASS — 1529 guard(s) checked, 361 invoked, 1149 orphaned (739 baselined as known unwired debt, rest justified), 0 NEW unwired, 0 copied hook(s)`

WIRE-ADVISORY (RED on main; wired `push_blocking=false` so the verdict is recorded on every push):
- `check-perf-regression-tests.shs` rc=1 — `FAIL — 191 mechanism(s) checked, 4 regressed: pure-interp array push through owner HOPPARK ...`
- `check-process-wait-eintr-retry.shs` rc=1 — `FAIL — selftest failed; gate cannot be trusted`

WIRE-BLOCKED (left unwired, reasons recorded):
- `check-use-target-resolves.shs` rc=1 — `FAIL — 332037 use(s) checked, 3274 new, 4854 stale: ...`
- `check-outline-parse-terminates.shs` rc=2 — `ERROR — nothing was checked (compiler 'bin/simple' not executable)` (needs a deployed binary; would ERROR on most push hosts)
- `check-test-tree-divergence.shs --ref origin/main` rc=1 — `FAIL — 3955 diverged vs 965 baselined (3085 new, 95 fixed-but-still-baselined); 26 mirror-only (25 unallowlisted, 0 stale-allowlist)`
- `check-unbacked-extern-ratchet.shs` rc=2 — `ERROR — nothing was checked: census failed (rc=2): ERROR — nothing was checked: no binary at .../bin/simple`
- `check-stage-binaries-runnable.shs` rc=1 — `FAIL — 3 invocation(s) executed across 1 binary(ies), 4 crashed/failed/wrong-arch: bootstrap/stage1/simple:wrong-architecture-for-host-at-unscoped-path(deploy-clobber,macho) ...`
- `check-no-unresolved-runtime-symbols.shs` rc=2 — `ERROR — nothing was checked (no readable symbol table: bootstrap/stage1/simple)`
- `check-seed-builds-push.shs` — **not classified**: exceeded a 10-minute budget on this host (cold `cargo check`). Too slow for an interactive push gate regardless of colour.

Note on PR #232: `check-stage-binaries-runnable.shs` names exactly the damage that
landed (`wrong-architecture-for-host(deploy-clobber,macho)`). It is RED for that very
reason, so wiring it blocking would block every push until the stage blobs are
repaired. It stays advisory-by-omission and is called out honestly in vcs.md.

## Second pre-existing finding: main is unpushable through the hook

The control run (unmodified `origin/main`, real dispatcher) ends:
`ERROR — nothing was checked (committed rules.sdl is not bound to the reviewed
policy digest)` -> `push-must-check: BLOCKING gate push-rules-quick failed (exit 2)`
-> `push-must-check: FAIL`. Every push to main today fails the hook at
`push-rules-quick`, which means the hook is being routed around with `--no-verify`
as a matter of routine. A guard set that everyone bypasses protects nothing; this is
the more urgent defect and is filed here rather than fixed in this change.

## Change

Five gates WIRED as **additional** push-tier rows in `config/check/must_check_gates.sdn`
(`push-c-runtime-compiles`, `push-no-direct-rt`, `push-guard-wiring` blocking;
`push-perf-regression-tests`, `push-process-wait-eintr-retry` advisory), plus five
matching case arms in `check-push-must-pass.shs`. Placed FIRST among push rows so they
execute ahead of the pre-existing `push-rules-quick` block.

**Why additive and not a tier move:** `validate_ledger_text` builds `manifest_seen`
from BOOTSTRAP-tier rows only, requires `manifest_count == ledger_count`, and rejects
any ledger id absent from it. The bootstrap rows are also named in
`REQUIRED_BOOTSTRAP_IDS` (`check-push-must-pass.shs:21`), an anti-deletion list.
Moving a row `bootstrap -> push`, or renaming it `push-*`, therefore makes the
dispatcher reject the ledger outright — observed twice as
`push-must-check: FAIL — ledger is malformed stale or has a non-passing push-blocking row`.
The bootstrap rows are left untouched; the push rows are a second, parallel
declaration, exactly as the existing 13 push rows already are (none of them has a
ledger row).

## Proof (dispatcher run, /mnt/data/gwaudit)

```
PASS — 128 file(s) compiled, 0 errors (2 skipped for unavailable external dependencies)
PASS — 16209 file(s) scanned (roots=src, src=6475), forbidden=6475, extern_decls=6467 (baseline 7776)
check-guard-wiring: PASS — 1529 guard(s) checked, 361 invoked, 1149 orphaned (739 baselined ...), 0 NEW unwired
FAIL — 191 mechanism(s) checked, 4 regressed: ...
push-must-check: ADVISORY push-perf-regression-tests verdict exit=1 (recorded, not blocking)
FAIL — selftest failed; gate cannot be trusted
push-must-check: ADVISORY push-process-wait-eintr-retry verdict exit=1 (recorded, not blocking)
```

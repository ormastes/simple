# TODO: hardening plan — resume after the bootstrap seed redeploy is stable

**Date:** 2026-08-25
**Status:** BLOCKED — waiting on a stable seed redeploy (bootstrap lane)
**Owner:** hardening audit lane (this session); resumes on unblock
**Plan:** `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md` §27–§28

## Why blocked

The deployed `bin/simple` (built 2026-08-23) is stale in three independent ways
and every remaining piece of evidence depends on replacing it:

1. predates the two JIT fixes landed in seed source (`c30d214b84a`, `3b676a17736`);
2. predates parser fix `d2d0bec2e40`, so it cannot parse the value-bound
   `unsafe(capabilities:)` form the stdlib adopted in `7ef30bafe0e` — every check
   driver importing `env_get` dies E1002, making `check-engine-differential`
   BLIND (`deployed_seed_cannot_parse_value_bound_unsafe_2026-08-25.md`);
3. loads a pre-fix stdlib copy from its own build tree (`seed-deploy-1`) alongside
   the current one (`io_runtime_read_file_still_aborts_incomplete_fix_2026-08-24.md`).

## Unblock condition

A seed built from `>= d2d0bec2e40` (ideally `>= 3b676a17736`) deployed to
`bin/release/<triple>/simple`, with `scripts/check/check-stage-binaries-runnable.shs`
green. "Stable" means: two consecutive `bin/simple --version` brackets across a
working day agree.

## Exact resume commands, in order

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"   # record identity
bin/simple run test/fixtures/engine_differential/value_bound_unsafe_block.spl   # must print 2 lines, no E1002
SIMPLE_TIMEOUT_SECONDS=0 nice -n 10 sh scripts/check/check-engine-differential.shs   # must print PASS/FAIL, not ERROR
sh scripts/check/refresh-critical-release-receipts.shs      # re-mint all receipts against the new artifact
sh scripts/check/check-critical-release-seal.shs             # read the real Phase 9 backlog
sh scripts/check/check-seed-selfhost-parity.shs              # needs a PURE-SIMPLE self; ERROR until one is deployed
```

## Acceptance tests already landed, waiting to be measured

All in `test/fixtures/engine_differential/` (the only lane that sees a
`simple run` vs interpreter divergence — `simple test` uses a different evaluator):

| fixture | pins | proven to bite |
|---|---|---|
| `option_of_enum_some_binding.spl` | both `case Some(x)` JIT fixes; three-stage bisector | deployed: crash / fix1: `through_binding=MISSING` / fix1+2: agrees |
| `gate_manifest_text_parse.spl` | the two gate-parser hoists over real tracked `.sdn` | hoists reverted: `pin_waivers=0 man_parse_errors=1` |
| `io_runtime_read_file_entry_points.spl` | all four text-read entry points | outside-tree on stale seed: rc=134 |
| `value_bound_unsafe_block.spl` | seed/stdlib `unsafe` parse skew | stale seed: E1002 before any output |

Expected on the new seed: all four AGREE across lanes.

## Still open after the redeploy (not blocked on it)

- `Some(x)` **layer 2**: untyped-param `.get` routed to the collection builtin before
  user-method resolution (`param: MISSING`); repro + fix sites in
  `jit_option_of_enum_payload_double_unwrap_2026-08-24.md`. Owner: JIT lane.
- `stmt_lowering.rs:1616` nested-struct-in-`Some` still uses `>= 0` (sibling of fix 1).
- Resolver: never load stdlib from the binary's build tree; never flatten one
  module from two roots. Owner: resolver lane.
- `check-critical-wildcard-ban`: 13 other lanes' buckets + 22 stale baseline
  entries; needs a reviewed `--generate-baseline` by the owners.
- §22.1 `reachable-unsupported=298` (criterion 0); §22.4 aspect steps 3–8.
- Phase 8: no package pinnable `critical` until Phase 7's gate can compare a
  real self-hosted binary.
- The shared working tree `/mnt/data/worktrees/simple-main` differs from origin
  in ~11,800 tracked files; backup at the session scratchpad `resync-backup/`.
  A full resync was deliberately NOT run (1,478 live build processes; 9,686
  mixed files may hold other lanes' work).

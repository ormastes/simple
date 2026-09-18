# TODO: hardening plan — resume after the bootstrap seed redeploy is stable

**Date:** 2026-08-25
**Status:** UNBLOCKED 2026-09-18 — seed redeployed; first resume pass run, results below
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


## Unblocked 2026-09-18 — resume pass run, with results

The unblock condition is met. `bin/release/aarch64-unknown-linux-gnu/simple` was
replaced with a seed built from `origin/main` that day:
`308de6af84db5c26e2c0…`, 51,645,288 B, 2026-09-18 17:03. It is far past both
`d2d0bec2e40` and `3b676a17736`. Record:
`doc/08_tracking/bug/seed_jit_optional_unwrap_returns_enum_box_2026-09-18.md`.

The old binary was worse than this todo knew: besides the three staleness
reasons above, it returned the Option BOX from `!` on the JIT lane, so
`Some("hello")! == "hello"` was silently `false`. That is why several records
measured on this host described already-fixed behaviour as broken.

### Resume commands, as prescribed, with their answers

| step | result |
|---|---|
| `bin/simple run …/value_bound_unsafe_block.spl` | **PASS** — prints its two lines (`home_nonempty=true`, `missing_is_nil=true`), no E1002. The parse skew that made the differential gate BLIND is gone. |
| `check-engine-differential.shs` | **produced a real verdict on its first run** — `FAIL — 1 unbaselined divergence among 19 fixtures`, where it had been reporting ERROR. |
| `check-seed-selfhost-parity.shs` | **ERROR — nothing was checked (self-hosted binary is the Rust seed)**, exactly as this todo predicted. Not a defect; it needs a deployed pure-Simple self. |
| `check-critical-release-seal.shs` | **FAIL — 12 evidence receipt(s) checked, 11 not fresh.** The one fresh receipt is `check-engine-differential` (`PASS`), minted by the run above. That is the real Phase 9 backlog this todo wanted read: 11 of 12 gates have never minted evidence against the current artifact. |

### What the first measurement found

The differential gate's single divergence was a genuine compiler defect, not
drift: `is_array_place_alias` (`mir/lower/lowering_stmt.rs`) carved out
`elem != TypeId::U8`, so a `val` bind or by-value pass of a `[u8]` ALIASED the
source buffer on the JIT lane while the interpreter copied it — the two engines
silently disagreed about the same source text. The carve-out's stated reason was
stale; both runtimes copy byte-packed arrays correctly. Fixed in PR #1090, gate
now `PASS — 0 divergences` over 19 fixtures.

**This is the argument for keeping gates unblinded.** The fixture and the gate
both already existed; the gate could not run for weeks, and a real miscompile sat
behind it the whole time. A gate reporting ERROR rather than PASS/FAIL is a
finding.

### Remaining work on this todo

1. `refresh-critical-release-receipts.shs` — not run here. It mints evidence for
   all 12 gates, which means actually running them; that is a long batch and
   deserves its own pass rather than being tacked onto this one.
2. The differential harness's **native lane still answers 0 of 19 fixtures**. Two
   blockers, one now removed: the SCV freeze is handled (the harness opts into
   `SIMPLE_SCV_FREEZE_FALLBACK`, since the fixtures live under `test/`, outside
   the `src` root the freeze covers), and the remaining one is the persistent
   package index (`scv-authority-missing`). Until that clears, a third of the
   gate's comparison surface is unavailable and the gate says so honestly.
3. `check-seed-selfhost-parity` stays ERROR until a pure-Simple self is deployed,
   which is the bootstrap chain's job, not this todo's.

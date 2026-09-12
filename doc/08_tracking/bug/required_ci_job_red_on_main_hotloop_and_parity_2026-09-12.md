# Required CI job `Code Idiom & Structural Ratchet Gates` red on `main` (hot-loop baseline + runtime source-list parity)

- Status: RESOLVED (2026-09-12) by the gate-sync commit this record ships with
- Component: `scripts/check/check-cpu-hotloop-idiom.shs` (+ `cpu_lane_hotloop_baseline.txt`),
  `scripts/check/check-runtime-source-list-parity.shs` (+ `runtime_source_list_parity_baseline.txt`)
- Impact: the ruleset's only required status check failed on every PR's merge
  tree, so nothing could land

## Observation (origin/main `4701188b9e0`, 2026-09-12)

1. `check-cpu-hotloop-idiom.shs` → `cpu_lane_hotloop_new=3 cpu_lane_hotloop_stale=1 cpu_lane_hotloop_ok=false`.
   Three new CPU-lane loops in `src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`
   (`while dx < r:`, `while dy < r:`, `while full < r and _emu_corner_cov256(...) >= 256:`)
   arrived with the engine2d landings (#547 `land/engine2d-rounded-rect-corner-aa`,
   #543 / #540 / #539 web-render / vulkan lanes) without a baseline update or a
   `# cpu-lane-loop-ok:` annotation, and one baselined key (`while px >= py:`)
   no longer exists in that file (stale). PR CI does not run this gate on the
   PR branch itself before merge, so it went red only once merged.
2. `check-runtime-source-list-parity.shs --rev origin/main` →
   `FAIL — 149 file(s) checked, 1 offender(s): browser/chrome_render_shim.c (new, not in baseline)`,
   from `9b95856a2ea` (2026-09-11, Chrome CEF dynlib boundary).

Seen as: PR #548's `Repo Hygiene Gate` run 34665544125 → job
`Code Idiom & Structural Ratchet Gates` steps "CPU-lane hot-loop hot-path
gate" (exit 1) and "Guard-wiring ratchet gate" (4 stale opt-out lines — the
four guards this session had opted out in PR #544 were wired on `main` by
#546 in the meantime, so those lines are dropped again here).

## Resolution (this commit)

- `cpu_lane_hotloop_baseline.txt`: regenerated with `--update-baseline`,
  diff-reviewed: +3 keys for the three `backend_emu.spl` loops (accepted as
  existing debt with this plan note — the engine2d lane owns moving them onto
  a bulk idiom or annotating them), −1 stale key, the rest is reordering.
  `cpu_lane_hotloop_ok=true` after.
- `runtime_source_list_parity_baseline.txt`: one hand-added row
  `browser/chrome_render_shim.c none` (dlopen-ed CEF shim, same design as
  `slang_ggml_shim.c`); header preserved (the generator discards it).
  `PASS — 149 file(s) checked, 0 drift` after.
- No opt-out lines: `check-guard-wiring.shs --rev origin/main` already PASSes
  (0 NEW unwired) since #546.

## Related

- `push_no_direct_rt_red_on_main_2026-09-12.md` — a third ratchet that is red
  and, separately, not enforced by the hook (ledger `todo`); left alone here.
- session memory `push-gates-red-on-main-2026-09-11`,
  `required-check-lives-in-repo-hygiene-gate`.

## Addendum: the push hook was also refusing every push from current main

`check-push-must-pass.shs` validates the committed ledger
`doc/08_tracking/check/must_check_db.sdn` against the manifest: every
bootstrap-tier manifest row needs a ledger row (`manifest_count !=
ledger_count → fail`). #547/#543 added two bootstrap-tier rows
(`chrome-web-showcase-perf`, `chrome-catalog-pixel-diff`) without ledger rows,
so the hook answered `ledger is malformed stale or has a non-passing
push-blocking row` for any branch based on `main` after them. Two `todo` rows
with owner and unblock condition are added here, matching the 2026-09-01
resync (a6137d15cfc).

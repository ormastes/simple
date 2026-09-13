# A spec that needs more than 900 s is killed and relaunched forever instead of failing

- **Filed:** 2026-09-13
- **Area:** app / test_runner_new (per-spec timeout budget)
- **Status:** FIXED 2026-09-13 (budget ladder + claim-before-execute).

## Fix

1. `src/app/test_runner_new/timeout_budget.spl` — `resolve_timeout_secs` is the
   documented ladder: explicit `--timeout N` > `SIMPLE_TIMEOUT_SECONDS` >
   900. `0` at either rung means unlimited (`TIMEOUT_UNLIMITED_SECS`, a
   365-day finite budget so every downstream "<= 0 means absent" hop keeps
   working and the daemon cap is bypassed). `timeout_value_is_well_formed`
   separates "the caller asked for no limit" from "the caller wrote junk",
   which the old parser could not: both returned 0.
2. `src/app/test_runner_new/test_runner_client.spl` — `--timeout`/`--timeout=`
   go through that ladder instead of `to_int`, so a malformed flag is ignored
   rather than becoming a 0-second budget.
3. `src/app/test_daemon/light_daemon.spl` + `light_protocol.spl` — a request is
   CLAIMED (renamed to a non-pollable `.req.inflight` name) BEFORE its spec
   runs, instead of being deleted after the response is written. A run killed
   at the budget is therefore attempted exactly once; the owning client emits
   its single `daemon-no-response` TIMEOUT verdict when its own deadline
   expires. No retry flag is offered: a retried timeout is the defect.

Specs: `test/01_unit/app/test_runner_new/client_timeout_env_spec.spl` (three
new scenarios: 0 = unlimited, flag > env > default, well-formedness) and
`test/01_unit/app/test_daemon/light_request_claim_spec.spl` (filesystem
round-trip; proven RED under a sabotage that makes a claimed request pollable
again). Contract documented in `doc/07_guide/infra/testing.md`.

## Symptom

`test/02_integration/ui/web_showcase/tab_switch_reuse_spec.spl` and
`overview_4k_render_spec.spl` never reach a verdict. The runner starts them,
kills them at roughly 900 s, and **starts them again**, indefinitely. Observed
by watching process elapsed time across polls: the process tree for one spec
repeatedly reset to `00:08`, `00:27`, `00:51`, `01:11`, `01:20` while the log
never advanced past the render phase and no `N examples, M failures` line was
ever written.

The failure mode is the problem: an over-budget spec should FAIL, visibly and
once. Relaunching hides it as "still running", which is indistinguishable from
a slow-but-healthy run. Two separate investigations in this session mistook
the loop for slowness.

## `SIMPLE_TIMEOUT_SECONDS=0` does not mean "no timeout"

This is the first trap, and it is in the documented invocation used across the
repo. `parse_env_timeout_secs("0")` returns 0, and
`client_default_timeout_secs` (`src/app/test_runner_new/timeout_budget.spl:58-64`)
treats any non-positive parse as "absent" and falls back to
`CLIENT_DEFAULT_TIMEOUT_SECS = 900` (`timeout_budget.spl:35`). So the common
incantation `SIMPLE_TIMEOUT_SECONDS=0 simple test <spec>` silently requests a
**900 s** budget, not an unlimited one. The child's own command line confirms
it: `simple test --no-session-daemon --timeout 900 <spec>`.

## Raising the budget did not help

Three attempts, all still capped and still looping:

| attempt | result |
|---|---|
| `SIMPLE_TIMEOUT_SECONDS=0` | child runs with `--timeout 900`; loops |
| `--timeout 2700` | prints `timeout: --timeout 2700s exceeds daemon cap; running directly`, then loops anyway |
| `SIMPLE_TIMEOUT_SECONDS=3000` | still restarted at ~14 min; loops |

So the effective ceiling is not reachable through either documented knob on
this host, and the "running directly" path does not escape it either.

`simple run <spec>` avoids the supervisor and is never killed, but is far too
slow to be an alternative: the same spec under `run` advanced its log by 5
lines in 15 minutes, versus reaching the render phase in ~4 minutes under
`test`.

## Why these specs need that long

One 320x180 Vulkan frame of a showcase page costs ~9-30 s here and a CPU frame
~23-60 s (see `web_showcase_4k_frame_time_unbudgeted_2026-09-13.md`), on top of
~4-5 minutes of module load per process. `tab_switch_reuse_spec.spl` was cut
from 8 renders to 5 to fit and still does not; `overview_4k_render_spec.spl`
does a single 3840x2160 frame measured at 177 s and still does not.

## Consequence for this change

Four of the six new showcase specs are verified green on this host
(`catalog_cpu_determinism`, `catalog_vulkan_twin`, `gpu_boundary_invariants`,
`chrome_dynlib_showcase`), two of them additionally proven to go red under a
deliberate sabotage. `tab_switch_reuse_spec.spl` and
`overview_4k_render_spec.spl` are landed **unverified**: they have never
produced a verdict, because of this loop and not because of anything observed
about their assertions. Both carry `@tag: ... slow`, so a default whole-suite
run does not pick them up. Treat them as unproven until this is fixed.

The evidence they are *meant* to assert was separately confirmed by direct
probe outside the runner: the 4K frame renders 8,294,400 non-blank pixels in
177 s with `cpu_fallback=false`, `readbacks=1`; and the A->B->A walk reproduced
tab A's digest exactly (`cd562909`) while `creates` stayed at 1 and `reuses`
advanced 3 -> 5.

## What is needed

1. An over-budget spec must FAIL once with a clear verdict, never relaunch.
2. `SIMPLE_TIMEOUT_SECONDS=0` should either mean "no limit" or be rejected —
   silently meaning 900 is worse than both.
3. A working way to raise the per-spec ceiling for genuinely long GPU specs.

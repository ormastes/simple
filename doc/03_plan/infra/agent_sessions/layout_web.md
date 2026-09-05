# Lane: Web Layout Interface (ex-codex 019fb81f)
Goal: concrete web layout manager interface (see `doc/03_plan/sys_test/web_layout_manager.md`, `layout_framework.md`).
Last state: work COMPLETE and pushed — `f80d51c1638` on `layout-web-layout-interface-clean`; session ended with "exit". Related main-repo commit: 4c6decd3056 feat(web): concrete layout manager interface.
Next: verify branch content merged/landed to main; then continue layout framework plan items (parent_id, iframe-as-embedded-batch per L4 lane notes).

## Plan audit 2026-08-01

Audited against `.spipe/layout_framework/state.md` (AC-1..AC-10) and
`.spipe/web_layout_manager/state.md`. Lane phase on the branch is
`implement-source-done` — **implementation only, never verified**. NOT truly
done. Actionable next steps:

1. **Land the branch to main and delete it** (no-branches rule).
   `layout-web-layout-interface-clean` tip `410d3d47482` is NOT an ancestor of
   `origin/main`. Land layout paths only — see item 2.
2. **Do NOT fast-forward/merge the branch wholesale.** It also carries 7
   unrelated gpu-mmu commits (`b06812e7208`..`410d3d47482`: object_vm
   descriptor_table, placement_backends, cas_store, gpu_mmu specs) that belong
   to the gpu-mmu lane, and `origin/main` has moved ahead on layout since the
   merge base `ae87d52fbdf` (notably `62a173b5c2e test(layout): CPU-reference
   oracle spec`). Main's `.spipe/web_layout_manager/state.md` is AHEAD of the
   branch's (`verify-static-warn` vs `interface-concrete`) — a naive merge
   REVERTS it. Land the layout delta file-by-file:
   `src/lib/common/structural/layout/engine.spl`,
   `test/.../layout/layout_framework_spec.spl`,
   `doc/03_plan/platform/structural_compute/{layout_framework,web_layout_manager}_plan.md`.
   Route the gpu-mmu commits to the gpu-mmu lane separately.
3. **AC-8 / AC-10 are UNMET — no runtime PASS exists.** The lane's own
   `verification-blocker` log entry: the deployed pure-Simple binary reports
   `unknown command 'check'` / `'test'` / `'spipe-docgen'`. Every acceptance
   claim is a static audit. Re-run the unit + system SSpecs once a working
   `bin/simple` is deployed and record real PASS counts.
4. **AC-9 generated operator-readable manual was never produced** —
   `spipe-docgen` was unavailable. Generate the mirrored manual after item 3.
5. **AC-7 GPU dispatch is source-only.** `hybrid_vector_gpu` cost-qualified
   homogeneous block/flex/grid dispatch is implemented but has no
   below/above-crossover runtime evidence; the lane explicitly deferred "GPU
   kernels and renderer-session wiring". Either land the crossover evidence or
   record the deferral as a scoped exclusion in the plan doc.
6. **Renderer-session wiring is still deferred** (`.spipe/web_layout_manager`
   "Deferred" line). The consumer-verification lane from
   `web_layout_manager_plan.md` is not closed.

## sspec sufficiency 2026-08-01

**Runner:** `bin/release/x86_64-unknown-linux-gnu/simple.pre-segv-fix-20260731`
(154MB) — the live `bin/simple` (130MB, Jul-31 12:14) has **no `test`/`run`/
`lint`/`check` subcommands at all**, confirming the known defect. Engine = the
`simple test` tree-walk path, but see the seed caveat below. Falsifiability
proven before use: a scratch spec with a wrong numeric oracle and a wrong text
oracle produced `3 examples, 2 failures` / `Results: 3 total, 1 passed, 2 failed`
/ exit 1, with both `assert_equal failed: expected 999, got 2` and
`expected beta, got alpha`. So numeric **and** text comparisons really fail —
the old native raw-pointer text-compare false-green is not active on this path.
This runner is also **not** fail-open: a nonexistent spec path exits 1 with
`error: test file not found`.

**Commit-reference correction.** The "engine dirty-propagation spec just landed
(~`56201aa5d41`)" pointer is wrong: `56201aa5d41` is
`fix(gpu-mmu): replace staged backend release placeholder and clean docs` and
touches only `src/lib/nogc_async_mut/gpu/placement_backends/staged_backend.spl`.
The actual recent layout-spec landing is `62a173b5c2e test(layout):
CPU-reference oracle spec for the spatial layout framework`, which is the
`layout_cpu_reference_oracle_spec.spl` run below.

### Run results

| spec | tier | result |
|---|---|---|
| `test/03_system/platform/structural_compute/layout_framework_spec.spl` | system | **3/3 PASS** |
| `test/01_unit/lib/structural/layout/layout_framework_spec.spl` | unit | 9/9 PASS |
| `test/01_unit/lib/structural/layout/layout_cpu_reference_oracle_spec.spl` | unit | 16/16 PASS |
| `test/01_unit/lib/gpu_web/layout/web_layout_manager_spec.spl` | unit | 4/4 PASS |
| `test/03_system/app/web_browser/feature/web_layout_manager_spec.spl` | system | **CANNOT RUN — `Process timed out`, exit 255, no `Results:` line at 600 s** |
| `test/03_system/app/web_browser/feature/web_layout_manager_wpt_parity_spec.spl` | system | **RED — 3 total, 0 passed, 3 failed** |

`test/01_unit/lib/gpu_web/layout/web_layout_incremental_oracle_spec.spl` was
also queued but was cancelled before completion and has **no result**.

**These results are trustworthy because of when they were taken.** They were
captured in a quiet window (04:02-04:09), each spec finishing in ~60 s. Shortly
afterwards the box degraded severely — load average 13 → 18 → 42 → **101** on 32
cores from competing sibling-worktree bootstrap builds — and from ~04:12 onward
*every* spec timed out, including a 3-example scratch probe that had passed in
~60 s earlier and then failed to finish in 400 s. The other three lanes audited
today could not be run at all for this reason. The layout numbers above predate
that collapse and stand.

The WPT parity failures are **not** assertion failures — all three report
`semantic: variable 'margin' not found`, i.e. the spec body does not resolve.
The parity oracle is therefore not merely failing, it is not executing.

### False-green risk observed (applies to all four lanes)

Every log contains `child binary:
/home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple` immediately
before the `N examples, M failures` block, together with
`WARNING: this Rust-built Simple binary is a bootstrap seed only`. **No
`SIMPLE_*` env var was set.** So `simple test` silently delegates spec execution
to the Rust seed (built Jul-31 01:38). Assertions do run (the falsifiability
probe failed correctly), so PASS/FAIL verdicts are real *executions* — but they
are **seed** verdicts, not pure-Simple self-hosted verdicts. For this lane that
is tolerable (the code under test is library `.spl`, which the seed compiles
from source), but no result here is evidence about the self-hosted compiler.

### Coverage verdict vs AC-1..AC-10

Covered by a passing system or unit spec: **AC-1** (contracts / versioned flat
input / profile catalog), **AC-2** (deterministic island partition), **AC-4**
(SCC condensation, topological waves, non-convergence fault), **AC-6**
(incremental == full over the oracle geometry, dirty-wave scheduling), **AC-3**
partially (one system `it` sweeps "every initial profile with fragments line
boxes and overflow").

Missing — named scenarios with no working system test:
- **AC-5 CPU-pipeline parity.** The only spec that cross-checks the new
  framework against the *existing* CPU pipeline is
  `web_layout_manager_wpt_parity_spec.spl`, and it is RED/non-resolving. The
  in-tree `layout_cpu_reference_oracle_spec` compares the framework to its own
  oracle, not to the shipping pipeline — that is not parity evidence.
- **AC-7/AC-8 above-crossover GPU dispatch.** Only the *below*-crossover half
  exists (CPU fallback for small/text/unsupported, heterogeneous-batch
  rejection, "reject a GPU claim without device readback"). There is no scenario
  in which `hybrid_vector_gpu` is actually dispatched and the geometry verified
  against a device readback. AC-8 explicitly demands **both** crossover
  decisions; only one is testable today.
- **Renderer-session / consumer wiring end-to-end.** The one system spec that
  would exercise it (`web_layout_manager_spec.spl`) times out and produces no
  verdict, so the consumer-verification lane has zero runtime evidence.
- **AC-9 (generated operator manual) and AC-10 (gate pass)** have no executable
  spec of any kind; they remain static-audit-only as the audit above states.

**Verdict: insufficient.** The core framework contract is genuinely green at the
system tier (3/3), which retires the "no runtime PASS exists" blocker in item 3
above for AC-1/2/4/6. But the two acceptance claims that carry the real risk —
CPU parity (AC-5) and above-crossover GPU dispatch (AC-7/8) — are respectively
RED-and-non-resolving and entirely absent, and the consumer-wiring system spec
cannot complete. Fix `web_layout_manager_wpt_parity_spec.spl`'s unresolved
`margin` binding first; it is the cheapest path to real parity evidence.


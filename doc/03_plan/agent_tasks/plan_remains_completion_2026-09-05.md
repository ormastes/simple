# Plan-remains completion (2026-09-05) — closing the four verification gaps

Companion to `plan_remains_acceptance_2026-09-05.md`. An adversarial
verification judged that lane NOT DONE on four counts (A-D below). This plan
lists the ordered work to close them, with the acceptance evidence for each
item stated as something that must be OBSERVED. Execution guides for smaller
agents live in `guides/` (one file per item; each ends with the checkbox rule).

Verification lane for every command here:
`SIMPLE_BINARY=$PWD/src/compiler_rust/target/debug/simple src/compiler_rust/target/debug/simple run <spec>`.
Discard any run whose output contains `E1034` (imports degraded to shims; a
matcher-less `expect("x")` passes vacuously under them). Scores are measured
with `sh scripts/check/sspec-score-seed-lane.shs <spec>`, never estimated.

## Checkbox rule (binding for every item below)

A box is ticked ONLY when the named acceptance `it`/command passes, with
`— verified <evidence>` appended on the same line (command + last verdict line
+ date). A ticked box without that suffix is treated as unticked.

## What holds and must not regress (re-measured 2026-09-05 during this work)

- 36 specs in `test/03_system/plan_acceptance/`; `sh scripts/check/check-plan-acceptance-coverage.shs`
  → `PASS — 36 plan(s) checked, 0 uncovered, 1 exempt` must stay so.
- Every spec touched here scores SCAN ≥ 90 (table in § B).
- The scorer's sha proof (`proof analyzer SAME sha256(src)=…`) is printed on every run.

---

## A — the headline property is exercised by nothing

### Measured root causes (this host, debug seed, 2026-09-05)

1. **The runner cannot execute a child spec when run from source.**
   `find_simple_binary` (`src/app/test_runner_new/test_executor_parsing.spl:55-66`)
   takes `cli_get_args()[0]`, which under `simple run <script>` is the SCRIPT
   (`argv[0]=build/probe/argv_probe.spl` measured), so the runner spawns the
   `.spl` as an executable → `Error: Compilation failed: ` (empty) and
   `outcome=NOT_RUN executed=0` for every child, tagged or not. `SIMPLE_BINARY`
   is not consulted there.
2. **Default Interpreter mode still reaches the native compile path** —
   `--verbose` prints `[native] Compiling …` (`run_test_file_native`,
   `test_runner_execute.spl:504`); the diversion point is not yet located.
3. **The existing integration spec's fixtures were corrupted by string
   interpolation**: `"use std.spec.{step}"` inside a text literal renders as
   `use std.spec.<fn:step>` (measured), so every generated fixture was a
   compile error. This is WHY only the crash path was ever observed. Fixed in
   the spec (`use std.spec.*`).
4. The seed's Rust `test` command has no in-development support; the spec's
   old `[binary, "test", dir]` invocation observed the wrong runner on seed
   hosts. Fixed: the spec now spawns
   `<binary> run src/app/test_runner_new/main.spl <dir>` (= `run_test_cli`).

### Verdict on this host

The neutralisation-of-a-failing-ASSERTION behaviour CANNOT be demonstrated
on this host today. Every child the runner spawns dies before executing
(`Compilation failed:` empty, `executed=0`), for the three reasons above, so
the only path ever observed is the crash path. Groups (a)-(d) of the
integration spec print ✓ through that crash path and are therefore not
evidence; group (e) is the only scenario that can tell the two apart and it
stays RED until A1 lands. The spec was NOT shaped to go green.

### Items

- [ ] **A1 — runner executes children on a seed host** (guide:
  `guides/gap_a_runner_child_binary_and_native_route.md`). Evidence: group (e)
  of `test/02_integration/test_runner/in_development_tag_runner_spec.spl`
  passes — the tagged fixture's own verdict line reads `executed=1 failed=1`,
  the output carries `expected 1 to equal 2`, no `Compilation failed`, no
  `E1034`, `IN-DEVELOPMENT SKIP … (1 expected failure(s)`, sweep exit 0; the
  untagged control exits non-zero with `1 failed` and no skip marker.
  Two new unit specs for the `find_simple_binary` fix (reproducing +
  generalisation, per testing.md).
- [ ] **A2 — harden the landed sweep gate** (guide:
  `guides/gap_a_plan_acceptance_sweep_gate.md`). A gate now exists
  (`scripts/check/check-plan-acceptance-swept.shs`, push row
  `push-plan-acceptance-swept`, advisory — landed 2026-09-05 while this plan
  was written, so the "nothing sweeps the directory" finding is closed at the
  coverage level). It still checks only `executed>0`; it cannot tell a
  neutralised REAL assertion failure (`executed=1 failed=1`) from a tagged
  spec that never loaded, has no `E1034` → ERROR rule, and has no
  bootstrap-tier row. Evidence: its selftest with the three new fixtures
  PASS; the real scan's last line; `check-guard-wiring.shs` PASS.
- [ ] **A4 — decision (plan owner): unresolved-import forcing functions vs the
  sweep gate's offender rule.** `spipe_knowledge_base_spec.spl` (staged `A`,
  mtime 15:52 — authored by a parallel session, NOT by this lead) is tagged
  in-development and imports the nonexistent `app.spipe.kb`, so it reports
  `executed=0` and the landed gate lists it as its one offender. That is the
  same sanctioned forcing-function pattern this lane's contract uses
  (render_perf A4/A7 import unimplemented modules the same way). Either the
  contract stops sanctioning unresolved-import pins (each must become a
  runnable `it` that fails on a real call), or the gate's rule distinguishes
  `load-failure` from `neutralised assertion` (Guide A2 item 1) and reports
  the former without failing. Evidence of the decision: the plan-remains
  contract text updated AND the gate's verdict on the kb spec matching it.
- [x] **A3 — the acceptance spec for the assertion-failure branch exists**
  — verified: written 2026-09-05 as group (e) of
  `test/02_integration/test_runner/in_development_tag_runner_spec.spl`
  (`REQ-INDEV-E1`, `REQ-INDEV-E2`); GATE 89 / SCAN 87 (this file is outside the
  plan-acceptance dir and its 90 floor; the residual findings are the
  pre-existing scenarios' missing `@req`/captures). **It is RED on this host
  until A1 lands** — the honest state, not a defect of the spec. Run log:
  see § Evidence.

---

## B — oracles that cannot fail (eight specs)

All eight rewritten by the lead. Every rewritten oracle pins ONE documented
value, pairs every scan with a non-vacuity control, and where the checkbox is
genuinely not done the `it` is RED and says why. Scores measured after the
rewrite (SCAN / GATE), run verdict on this host, and the planted control:

| spec | SCAN / GATE | verdict on this host | RED-by-design? | planted control (see § Evidence) |
|---|---|---|---|---|
| `dependency_analysis_spec.spl` | 97 / 100 | 2/3 — `load_module_lazy` returns 0, registry stays 0 (probe: `gate=0 before=0 rc=0 after=0`) | yes: W2-A2 bridge does not register a real module | gate default forced ON in a copy of the module → scenario 1 red (planned; run after A-runs settle) |
| `scilib_port_ndarray_spec.spl` | 93 / 96 | 6/7 — REQ-06 red: 5 non-underscore `fn` signatures carry primitives | yes: checkbox :831 genuinely open | planted `nvfortran` file in the ndarray dir → REQ-01 red `expected 1 to equal 0`; removed, verified gone |
| `fpga_board_bringup_jtag_10min_plan_spec.spl` | 96 / 99 | 1/2 — transcript scenario red: no board transcript on this host | yes: no KV260 attached; OpenOCD path blocked on tunnel interop | planted transcript → 2/2 GREEN; IDCODE corrupted in it → transcript scenario RED; removed |
| `startup_perf_plan_spec.spl` | 95 / 98 | 2/3 — Phase E now GREEN on real inputs (baseline parsed from the metrics doc = 1298, current closure recomputed by the deps scanner, `within_band`); Phase C red (pre-existing: completion candidates `[]`) | Phase C only, pre-existing | metrics cell 1298→1299 → Phase E red; doc restored (git diff clean) |
| `render_perf_redesign_plan_spec.spl` | 97 / 100 | 0/5 — A4/A7 modules absent; A5 `preflight_rejected` (no Vulkan); A6 wrapper blocked; A8 no 7680x4320@80 display | yes, all five: physical/Vulkan hardware absent; A4/A7 modules unimplemented | fake `system_profiler` on PATH reporting `7680 x 4320 @ 80.00Hz` → A8 green; removed |
| `aarch64_darwin_contract_snippet_spec.spl` | 92 / 95 | 3/4 — sibling sys spec reports `missing-media:build/os/darwin-aarch64/simpleos_aarch64_darwin_fs_exec` on this darwin host (binary not staged) | yes: darwin binary not built here | in-spec: driver calling a nonexistent accessor must not run clean (passes); bogus kernel path → verdict names THAT path (passes) |
| `aspect_dynload_lane_plan_spec.spl` | 97 / 100 | 32/40 — identical 8 failures at HEAD (pre-existing, none of them the two rewritten `it`s) | pre-existing only | in-spec: `required == 0x03FFFFFF`, `mask <= required`, owned `.rs` census 0 with total > 0; fresh loader `hits == 0`, slot key deterministic and index-sensitive |
| `excel_to_math_lib_migration_spec.spl` | 92 / 94 | 4/5 — "All formula tests pass" red at HEAD (pre-existing) | pre-existing only | `direct_us > 0` (a 20000-call loop must advance the clock) |
| `sycl_parity_unified_kernel_plan_spec.spl` (added W3.2 `it`) | 97 / 100 | 4/5 — new W3.2 `it` red: `expected 0 to equal 2` — the real parser accepts `@unroll(4) @pipeline(ii=3) @memory(banks=2)` but the decl slots read 0 (setters never called); HEAD version was 4/4 | yes: W3.2 genuinely unwired (Gap C's own finding) | in-spec: undecorated fn reads 0/0/0; the positive branch is the forcing function |

Note on the coverage check: the committed untick of sycl W3.2 (Gap C) made
that plan 5 open boxes against a 4-`it` spec, so
`check-plan-acceptance-coverage.shs` was FAILING at HEAD
(`short:sycl_parity_unified_kernel_plan(4/5)`). The added W3.2 `it` restores
`PASS — 36 plan(s) checked, 0 uncovered, 1 exempt` (re-measured after the edit).
Guide C must re-run the coverage check after every untick for the same reason.

RED-by-design list for this host, so red is not misread as breakage:
depa scenario 3; scilib REQ-06; fpga transcript; render A4-A8; aarch64
scenario 3; in-development group (e) until A1.

Implementation guides for the genuinely-open items:
`guides/gap_b_dependency_analysis_w2a2_bridge.md`,
`guides/gap_b_scilib_ndarray_primitive_signatures.md`,
`guides/gap_b_render_perf_a4_a7_receipts.md`,
`guides/gap_b_aarch64_darwin_staging.md` (darwin host),
`guides/gap_b_fpga_openocd_transcript.md` (board operator).

- [ ] **B1** depa W2-A2 — evidence: `dependency_analysis_spec.spl` → `3 examples, 0 failures`.
- [ ] **B2** scilib REQ-06 — evidence: `scilib_port_ndarray_spec.spl` → `7 examples, 0 failures`.
- [ ] **B3** render A4 receipt module — evidence: A4 `it` ✓ (A7 stays red until A6 evidence).
- [ ] **B4** aarch64 darwin staging — evidence: `4 examples, 0 failures` on a darwin host with `[aarch64-darwin-sibling] … outcome=OK`.
- [ ] **B5** fpga OpenOCD transcript — evidence: `2 examples, 0 failures` with the transcript's sha256 and board serial recorded.

---

## C — false ticks

The three named instances are ALREADY corrected at HEAD (a parallel session
landed them; re-checked 2026-09-05): sycl :88 unticked with the zero-call-site
reason; perf_checklists :212 citation replaced and every cited line resolves
(`syscall_shim_process.spl:338`, `user_entry_bridge.spl:21-24`,
`vmm_address_space.spl:314`); aspect_dynload :401 unticked.

- [ ] **C1 — audit every `[x]` that cites a plan-acceptance spec** (guide:
  `guides/gap_c_false_tick_audit.md`). Evidence: `build/tick_audit/list.txt`
  non-empty; every untick carries `— UNTICKED 2026-09-05: … (<verdict line>)`;
  coverage check still `PASS — 36 plan(s) checked, 0 uncovered`.
- [ ] **C2 — sycl W3.2 bug record** filed naming `enum_module_body.spl:25`
  and the setters at `_Ast/decl_nodes.spl:1260-1278`, unblock = a real call
  site + `vhdl_kernel_attrs_contract_spec.spl` green.

---

## D — `check-no-direct-rt.shs` FAIL (re-classified: NOT a red gate)

The verification's "Gap D" was a measurement error, confirmed by the
coordinator 2026-09-05: both wired manifest rows use `--roots src` and are
green. Items D1/D2 below are hardening (make the incomparable bare run a
fail-closed ERROR; plan the test-tree reduction), not the repair of a red gate.

Measured: the WIRED push row (`--roots src`) is GREEN —
`PASS — 16244 file(s) scanned (roots=src, src=6230) … (baseline 7776)`. The
FAIL is the bare default invocation (`roots=src,examples,tools,scripts,test`,
forbidden 27454) compared against a baseline the script's own header says is
only comparable to `roots=src`. No re-baseline.

- [ ] **D1 — baseline records its roots; mismatch is a fail-closed ERROR**
  (guide: `guides/gap_d_no_direct_rt_scope_and_reduction.md`). Evidence: bare
  run → `ERROR — nothing was checked (baseline recorded for roots=src …)` exit 2;
  `--roots src` unchanged PASS; selftest fixture for the mismatch.
- [ ] **D2 — test-tree reduction plan** — evidence:
  `doc/08_tracking/todo/no_direct_rt_test_reduction_2026-09-05.md` with the
  per-symbol table summing to the measured `test=19558` (top dirs:
  `01_unit/compiler` 2559, `01_unit/lib` 2458, `01_unit/app` 1157,
  `01_unit/os` 858, `03_system/feature` 780, `03_system/os` 737).
- [ ] **D3 — decision (plan owner, not an agent):** whether to open a second,
  ADVISORY ratchet for `roots=test` with its own first baseline. Recording a
  first baseline for a scope that never had one starts a ratchet rather than
  stopping one, but it is still a baseline write and is therefore a decision,
  not a default.

---

## Evidence (transcripts, 2026-09-05, debug seed, macOS aarch64)

Gap A reproduction (fixtures in a scratch dir, runner from source):

```
IN-DEVELOPMENT SKIP …/indev_fail_spec.spl (1 expected failure(s); @tag:in-development)
  FAIL  …/plain_fail_spec.spl (0 passed, 1 failed, 85ms)
        Error: Compilation failed:
SPEC FILE VERDICT: …/indev_fail_spec.spl outcome=NOT_RUN declared>=0 executed=0 passed=0 failed=0
[--verbose] [native] Compiling …/plain_fail_spec.spl to …smf
argv probe: argv[0]=build/probe/argv_probe.spl
interpolation probe: "use std.spec.{step}" → use std.spec.<fn:step>
```

Planted controls (each followed by restoration; `git diff` clean afterwards):

```
scilib REQ-01: planted src/lib/nogc_async_mut/ndarray/zz_planted_control_spec_probe.spl containing "nvfortran"
  ✗ No `nvfortran` dependency added — expected 1 to equal 0        (restored: file gone)
fpga: planted build/fpga/evidence/openocd_halt_regs_step.log (board line, tap/device found: 0x15350067, halted, pc, step, resume)
  ✓ transcript scenario, ✓ codec → outcome=OK
  IDCODE edited to 0x15350068 in the planted file
  ✗ transcript scenario, ✓ codec → outcome=ERROR                    (restored: file removed)
```

```
startup_perf Phase E: metrics cell `**1298**` edited to `**1299**` in doc/10_metrics/startup/coupling_cohesion_baseline_2026-08-17.md
  ✗ Phase E — expected 1299 to equal 1298                            (restored: git diff --stat → 0 lines)
render_perf A8: fake `system_profiler` first on PATH printing "UI Looks like: 7680 x 4320 @ 80.00Hz"
  ✓ A8 (only A8 changed; A4-A7 stay red)                             (restored: fake tool removed)
```

PENDING at the time of writing (chained behind the in-development spec run,
which was still in group (d) — each scenario spawns the runner from source
and takes minutes on this loaded host): (1) group (e) verdict — expected RED
with `Compilation failed` / `executed=0` until A1 lands; the ✓ lines in
groups (a)-(d) are produced THROUGH the crash path and are not evidence of
the feature; (2) depa gate control — `lazy_parse_enabled` forced to read
`"1"` by a temporary module edit, scenario 1 expected RED, module restored
from a byte copy and checked with `git diff --stat`. Post-restore reruns completed:
scilib → REQ-01 ✓ again (only REQ-06 red, 6/7); startup_perf → Phase E ✓
again (`within_band` on the real 1298 baseline, 2/3 with Phase C
pre-existing red). Both restored trees are byte-identical to HEAD
(`git diff --stat` → 0 lines). In-development spec run COMPLETE (no `E1034`, exit 1, 5/9): groups (a)-(c)
✓ (crash path), group (d) both ✗ — a tagged PASSING fixture cannot pass
either — and group (e) both ✗ exactly as predicted:
```
  ✗ executes the tagged spec's `it`, sees the real assertion failure, and still neutralises it
    SPEC FILE VERDICT: .../wip_failing_spec.spl outcome=NOT_RUN declared>=0 executed=0 ...
    (output does not contain "expected 1 to equal 2" — the assertion never ran)
  ✗ reddens the sweep for the IDENTICAL assertion when the tag is absent (control)
    expected true to equal false   (= "Compilation failed" present: crash path, not the assertion)
```
This is the measured proof that the neutralisation-of-a-failing-assertion
branch has not been exercised on this host; group (e) is the gate A1 must
turn green.

Depa gate control COMPLETE: `lazy_parse_enabled` forced to read `"1"` by a
temporary edit of `module_loader_lazy.spl`:
```
  ✗ W2-A2: outline-parse module ... gated by SIMPLE_LAZY_PARSE=1 — expected 1 to equal 0
  ✓ lazy_scan_probe ...   ✓ load_module_lazy registers ...
```
Module restored from the byte copy taken before the edit (`cmp` → identical;
the `PLANTED CONTROL` marker is gone). `git diff` on that file is NOT empty,
but the residual hunk is a PARALLEL session's uncommitted edit that was
already in the working copy before the control (`_lazy_compiler_numbered_candidate`,
a `compiler.<NN>.<name>` resolver candidate) — not mine. Side effect worth
knowing: with that uncommitted edit present, depa scenario 3
(`load_module_lazy` → 1, registry flips 0→1) now PASSES, i.e. the RED-by-design
entry for depa in the § B table reflects HEAD; once that parallel edit lands,
B1 may already be satisfied — re-run the spec before assigning Guide B1.

Direction of each control, stated so red is not misread: scilib REQ-01,
startup Phase E, depa gate — GREEN normally, plant → RED, restore → GREEN.
fpga transcript, render A8 — RED-by-design normally, plant → GREEN, corrupt /
remove → RED.

## Measured sweep runtime — pooled gate reaches a verdict in 17 min; the 4-13 min estimate is still WRONG (2026-09-06)

`scripts/check/check-plan-acceptance-swept.shs` landed advisory partly on an
estimated "4-13 min serial" cost. It has since been refactored from a serial
loop to a bounded worker pool (`--jobs N` / `PLAN_ACCEPTANCE_JOBS`, default =
online CPUs capped at 8). The push row's description in
`config/check/must_check_gates.sdn` still says `~13 min serial` — stale on
both counts.

### Superseded history — the SERIAL gate (kept, not deleted)

Measured twice before the pool existed, both timed out at **2400s without
reaching a verdict line**:

- the gate itself, `PLAN_ACCEPTANCE_RUNNER=<debug seed> SIMPLE_MCDC_MODE=off`
  — worked alphabetically through the specs, no verdict at 40 min;
- a direct suite sweep of the same directory — graceful checkpoint shutdown,
  exit 42, `To resume tests, run: simple test --resume`.

`startup_perf_plan_spec.spl` alone took **287s** in that lane. These numbers
describe a gate that no longer exists in that form; they are retained so the
"4-13 min" estimate is never re-derived from them.

### Current — pooled run, 2026-09-06

`--jobs 8`, runner `src/compiler_rust/target/debug/simple` via
`PLAN_ACCEPTANCE_RUNNER`, `SIMPLE_MCDC_MODE=off`:

- wall **1029s (17m09s)**, rc=1, verdict line reached; selftest 14/14 (fatal
  before the scan, as designed).
- `specs_attempted=36`, `specs_loaded_and_ran=32`,
  `specs_with_example_failures=26`, `in_development_tagged=36`, `coverage=ok`.
- `FAIL — 36 spec(s) executed ..., 44 failed to load/run or neutralise cleanly`.

The 44 decomposes exactly: 4 genuine 300s per-spec timeouts
(`excel_to_math_lib_migration`, `excel_to_math_synthesis`,
`rsa_modexp_montgomery_barrett`, `startup_perf_plan`) + 40 ×
`load-failure-neutralised` = **every one of the 36 tagged specs** (15 named,
21 `(no-marker)`), with `N_NEUTR_ASSERT=0`. Read literally, the gate claimed
that not one tagged spec in the directory neutralised a real assertion — while
`specs_loaded_and_ran=32` and `specs_with_example_failures=26` in the same
verdict say most of them loaded, ran, and failed examples. That contradiction
is the root cause below, not 36 broken specs.

### Root cause — CONFIRMED and FIXED

`ran_verdict_line` (`src/app/test_daemon/light_protocol.spl`) computed
`executed = passed + failed`. `in_development_adjust` neutralises a tagged
file to `passed=0, failed=0, skipped=N`, so the aggregating (directory) lane
printed `outcome=NOT_RUN declared>=0 executed=0` for every neutralised file —
byte-identical to a file that never loaded. Any sweep that classifies on that
line must read a correctly-neutralised spec as a load failure. The single-file
lane was unaffected (it reports the failures as real failures), which is why a
per-spec run and a directory run of the same file disagreed.

The earlier hypothesis that specs broke because the gate `cp`s them out of the
repo into a `mktemp -d` shard is **REFUTED**: the confirming probe ran from an
in-repo directory and reproduced the defect there.

Fix landed: `in_development` — a field that already existed on
`TestFileResult`, documented as distinct from environment skips — is now set
by `in_development_adjust`, counted toward `executed`, and emitted as
`in_development={n}`; the gate classifies on it. Environment skips are
deliberately still NOT counted, so an all-skipped file cannot greenwash itself
to `outcome=OK`. Verified through the real runner:
`NOT_RUN executed=0` → `OK executed=9 in_development=9`, matching the SKIP
markers' 9 and 8.

Why the selftest never caught it: its fake runner emitted `failed=1` for a
neutralised file — a shape the real lane never produces — so 14/14 passed
against a defect the fixture could not exhibit. Corrected: the old classifier
now fails the selftest that reproduces production exactly, and passes with the
fix. Lesson for every gate in this plan: **a fixture that cannot exhibit the
defect is not a test for it.** The A2 selftest evidence bar above is read with
that in mind.

**PENDING: a full re-run of the gate with the fix is in flight and its result
is not known at the time of writing.** No post-fix offender count is stated
here, and none should be inferred from the decomposition above. The 300s cap
is per-spec wall time and the fix touches verdict-line classification only, so
the re-run measures both populations afresh; nothing about what count survives
is known until it lands. Record the verdict line under § Evidence when it lands.

### Per-item status of the § B remains after this measurement

The pooled run reports per-directory counters, not per-spec example lines, so
it can confirm or contradict § B only where a spec is named in the offender
list. Everything else in this list is the § B table's own claim, unchanged and
not re-verified by the sweep.

- **B1 depa W2-A2** — not named as a timeout; no per-spec evidence from the
  sweep. § B / § Evidence note that an uncommitted parallel edit may already
  satisfy it; still UNVERIFIED at HEAD. Open.
- **B2 scilib REQ-06** — not named as a timeout; no per-spec evidence from the
  sweep. Open, RED-by-design per § B.
- **B3 render A4 receipt** — not named; no per-spec evidence. Open,
  RED-by-design (modules absent).
- **B4 aarch64 darwin staging** — not named; no per-spec evidence. Open,
  RED-by-design (binary not staged).
- **B5 fpga OpenOCD transcript** — not named; no per-spec evidence. Open,
  RED-by-design (no board).
- **Correction to § B, `excel_to_math_lib_migration_spec.spl`** — the table
  records `4/5` on this host; under the pooled gate it **timed out at 300s**
  and produced no verdict. The `4/5` was measured in the single-file lane (line 10),
  not under the gate's 300s cap, so the two are not contradictory, but the spec cannot currently be swept
  by the gate as configured. Same for `startup_perf_plan_spec.spl` (table:
  `2/3`; serial lane 287s; timed out at 300s in the pooled lane). `excel_to_math_synthesis` and
  `rsa_modexp_montgomery_barrett` are not § B specs but share the fate.
  Whether the cap should rise, the specs should shrink, or the timeouts should
  be a separate offender class with their own count is part of the gate-home
  decision below; not decided here.
- **A2 / A4** — the load-failure-vs-neutralised-assertion distinction A2 item 1
  asked for is now the mechanism the gate classifies on, and A4's kb-spec
  offender should now be reported as a genuine load failure rather than lost
  among 40 false ones. Neither box is ticked: both wait on the pending re-run's
  verdict line, and A4 still needs the contract-text decision.
- **In-development tag coverage** — `in_development_tagged=36`: every spec in
  the directory is tagged. That is the sweep's premise (a tagged failure is
  neutralised, not red), and it also means the directory contains zero
  untagged controls; the only untagged control in this plan remains group (e)
  of the integration spec (A1).

### Gate home — inputs are now real; the decision is NOT taken

17 min pooled on an 8-way host, with `bin/simple` on most push hosts unable to
run it at all (the gate ERRORs, exit 2, without a runnable runner — its own header, `check-plan-acceptance-swept.shs:65`, and selftest fixture "missing runner is ERROR not PASS", `:627`).
`.claude/rules/vcs.md` kept `check-seed-builds-push.shs` out of the push tier
for exceeding 10 minutes, and records that a guard routed around with
`--no-verify` protects nothing — a 17-min blocking push gate would be routed
around on day one.

| home | cost per event | what it actually enforces | honest problems |
|---|---|---|---|
| push, blocking | 17 min on an 8-CPU host; ERROR (exit 2) on any host without a runnable runner (script `:65`, selftest `:627`) | every push | over the 10-min bar; blocks binary-less hosts on ERROR; will be `--no-verify`d |
| push, advisory (**current**) | same 17 min, verdict recorded on stderr only | nothing — an advisory verdict is never a pass, and nothing reads it | the cost is paid and the protection is zero; row description still says `~13 min serial` |
| bootstrap tier | 17 min once per bootstrap, on a host that by construction has a runnable compiler | the deployed compiler's acceptance sweep | a row `plan-acceptance-swept` already exists at `tier=bootstrap` in `config/check/must_check_gates.sdn` beside the advisory push row; **whether a bootstrap-tier FAIL is gated by a receipt/ledger entry, or is merely recorded, is UNVERIFIED** — read `run_manifest_push_gates` and the bootstrap admission path before relying on it |
| sampled subset on push | ~17 min × k/36 (k stated in the verdict line, e.g. `k=6` ≈ 3 min) | a rotating slice; full coverage only over ~36/k pushes | a sample that misses the broken spec is a green verdict; k and the seed must be in the verdict line or the run is unauditable; 4 specs exceed the cap and would need exclusion or a raised cap, which must also be recorded |

Recommendation of the plan owner, pending the re-run: **bootstrap tier as the
enforcing home, push row demoted to a documented no-op or removed**, because
the gate needs a runnable compiler and 17 min is a bootstrap-scale cost, not a
push-scale one; a sampled push subset is acceptable ONLY as an addition and
ONLY with k, seed and the excluded-timeout list printed in the verdict. Before
that can be enacted: (1) the pending re-run must reach a verdict; (2) the
bootstrap-tier enforcement question above must be verified, not assumed; (3)
the stale `~13 min serial` row text must be corrected in the same change. None
of these has happened. The decision is not taken.

### What the serial sweeps DID establish (still valid)

Even without a verdict line, the serial runs showed the goal's item 1 at suite
scale rather than fixtures: 8 specs neutralised with distinct per-spec failure
counts across six unrelated domains — cuda_host_validation,
scilib_port_math_block, office_cli_tui_ui_access,
compiler_loader_script_crosslang_perf, excel_to_math_lib_migration,
excel_to_math_synthesis, unified_compute_stdlib_rollout, perf_checklists —
plus `IN-DEVELOPMENT UNEXPECTED PASS fat32_atomic_replace_recovery_spec.spl
(10 example(s) passed) — ready to promote`. The pooled run's
`specs_with_example_failures=26` is the same phenomenon counted by the gate
rather than read off the transcript.

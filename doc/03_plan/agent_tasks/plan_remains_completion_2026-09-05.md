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

- 35 specs in `test/03_system/plan_acceptance/`; `sh scripts/check/check-plan-acceptance-coverage.shs`
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

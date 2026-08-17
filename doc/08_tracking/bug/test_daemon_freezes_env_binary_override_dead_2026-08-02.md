# The test daemon freezes the environment, so a binary override is silently dead

- **Date:** 2026-08-02
- **Status:** fixed (client-side lane bypass); protocol-level fix still open
- **Severity:** measurement integrity — affected specs fail silently *green*
- **Evidence tier:** Rust seed (`bin/simple`; bootstrap-identity probe
  `strings bin/simple | grep -c "enum construction: unregistered enum"` = 0)

## Summary

`bin/simple test <spec>` does not normally run the spec in the process you
launched. When the request qualifies (`test_should_use_light_daemon_client` in
`src/compiler_rust/driver/src/main.rs`), the path is handed to a long-lived
helper, `src/app/test_daemon/light_daemon.spl`, through a request file.

The v1 request encoding carries **no environment**:

```
fn light_request_encode(path: text, expiry_micros: i64) -> text:
    "{LIGHT_REQUEST_V1_HEADER}\n{expiry_micros}\n{path}"
```

The daemon's own environment is whatever the invocation that first started it
happened to have, and it then outlives that invocation by minutes. Every
subsequent `bin/simple test` run therefore executes spec bodies under a
**stale, frozen environment** — silently.

For the ~39 specs that resolve *which binary they exercise* from the
environment, this means the override the caller named is discarded and the spec
goes on testing the default `bin/simple` under the name of the selected one.

## Reproduction (measured)

```
$ <kill any running light_daemon>
$ SIMPLE_TEST_BINARY=VALUE_FIVE bin/simple test <probe> --no-db
PROBE env_get(SIMPLE_TEST_BINARY)=[VALUE_FIVE]     <- correct, this run started the daemon
PROBE SHELL_SEES=[VALUE_FIVE]

$ SIMPLE_TEST_BINARY=VALUE_SIX  bin/simple test <probe> --no-db
PROBE env_get(SIMPLE_TEST_BINARY)=[VALUE_FIVE]     <- WRONG: replays the previous run
PROBE SHELL_SEES=[VALUE_FIVE]                      <- WRONG
```

An unrelated variable set only in the *first* run (`SIMPLE_MEM_PROBE_SENTINEL=HELLO`)
also kept reappearing in later runs that never set it, which is what identified
the frozen-environment mechanism. The process holding it was confirmed directly:

```
pid=2067913 cmd=src/compiler_rust/target/debug/simple run src/app/test_daemon/light_daemon.spl
```

## The workaround that does NOT work

Commit `c6e30f3a745` diagnosed this as "the runner does not surface that
variable to spec bodies" and fixed it by resolving the override in the child
shell — `"${SIMPLE_TEST_BINARY:-bin/simple}"` — instead of via `env_get`.

**That does not fix it.** The child shell is forked *by the daemon*, so it
inherits the daemon's frozen environment too. In the transcript above,
`SHELL_SEES` is wrong on exactly the same runs where `env_get` is wrong. The
shell form appeared to work only because the run that exercised it happened to
be the run that started the daemon.

The true axis is not *how the spec spells the lookup* — it is *which process
the spec body runs in*. Both spellings are live with no daemon running, and
both are dead with a stale one.

## Fix

`src/app/test_runner_new/test_runner_client.spl` already carried the precedent:
`SIMPLE_COVERAGE` bypasses the daemon lane because "the daemon's environment
predates this request". The binary-override family is the same defect class,
one step worse because it fails silently rather than merely under-reporting.

Any request naming `SIMPLE_TEST_BINARY`, `SIMPLE_BINARY`, `SIMPLE_BIN`,
`SIMPLE_SEED_BINARY` or `SIMPLE_SPEC_COMPILER` now takes the direct lane. None
of these is set in a normal run, so the daemon lane is unaffected on the hot
path.

Verified after the fix, with a daemon alive throughout:

```
binary-override: SIMPLE_TEST_BINARY set; bypassing test daemon so the override reaches the spec
PROBE env_get(SIMPLE_TEST_BINARY)=[VALUE_SEVEN]
PROBE SHELL_SEES=[VALUE_SEVEN]
```

Regression coverage:
`test/03_system/check/test_daemon_env_override_passthrough_spec.spl`
(deliberately seeds a daemon from a non-overridden invocation first, then
asserts both channels observe the caller's value).

## Follow-up 2026-08-04: the fix was not closed over the family

The list above names five variables. A census of `env_get("…")` across all
20,310 tracked spec files found **16 further spec files** that select a binary,
backend or toolchain from a variable that was *not* on it. Every one of them was
still dead.

Decisive probe (`test/fixtures/mem_infra/env_selector_probe_spec.spl`, a
generalisation of the single-name fixture; Rust seed, bootstrap-identity probe
= 0). The daemon PID was recorded before and after every run:

| run | environment | daemon | spec body observed |
|-----|-------------|--------|--------------------|
| B | six sibling selectors = `BRAVO` | *started* by this run (PID changed) | `BRAVO` — the misleading case |
| C | same six = `CHARLIE` | 3112464, unchanged | **`BRAVO`** — DEAD, both channels |
| D | same six = `DELTA` **plus** `SIMPLE_TEST_BINARY=DELTA` | 3112464, unchanged | `DELTA` — bypass works |
| E | same six = `ECHO`, after the list was expanded | 3287410, unchanged | `ECHO`, and the runner printed the bypass line naming the siblings |

Run D differs from run C *only* by naming an allowlisted variable, so membership
in `_binary_override_vars()` is exactly what makes a selector live. Run B is the
trap the original report already warned about and is worth restating: a run that
happens to start the daemon reports correctly, so a one-shot check of a dead
override looks green. Always compare the daemon PID across the two runs.

Sixteen affected files, by the variable that was dead:

| variable | spec files |
|----------|-----------|
| `CPU_SIMD_RENDER_SCALE_TEST_SIMPLE_BIN` | test/03_system/check/cpu_simd_render_scale_contract_spec.spl |
| `SIMPLEOS_QEMU_SIMPLE_BIN` | test/03_system/os/qemu/os/scheduler/green_carrier_qemu_spec.spl |
| `SIMPLEOS_DBFS_BOOT_QEMU_EXEC` | test/03_system/os/port/dbfs_disk_boot_spec.spl |
| `SIMPLE_HOSTED_BROWSER_EXECUTABLE` | test/05_perf/browser/hosted_browser_process_pipe_perf_spec.spl |
| `DEVHUB_MAIL_BIN` | test/01_unit/app/devhub/email_cmd_spec.spl |
| `T32_PYTHON_BINARY`, `T32_BACKEND_PREFERENCE` | test/02_integration/t32_hw/t32_hw_helpers.spl, test/integration/t32_hw/t32_hw_helpers.spl |
| `LLVM_BUILD` | test/integration/os/port/llvm/smoke_clang_spec.spl |
| `SIMPLE_MMU_DIRECT_BACKEND`, `SIMPLE_MMU_DEVICE_INITIATED_BACKEND` | test/03_system/lib/gpu/object_vm/gpu_mmu_spec.spl, test/01_unit/lib/nogc_async_mut/gpu/placement_backends/placement_backends_spec.spl |
| `SIMPLE_WEB_GPU_PAINT_MEASURE_BACKEND` | test/05_perf/web_render_chrome/web_gpu_paint_device_measured_spec.spl, test/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.spl |
| `SIMPLE_GPU_COMPILER_{PRODUCER,RUNTIME_PATH,*_SHA256}` | test/03_system/compiler/native_cli_mode_transport_regression_spec.spl |
| `SIMPLE_NATIVE_BUILD_TARGET` | test/01_unit/app/compile_targets_env_facade_source_spec.spl |
| `SIMPLE_ENGINE2D_RUNNER_MODE`, `SIMPLE_ENGINE2D_FULL_MODE` | test/05_perf/graphics_2d/simple_runner.spl, test/perf/graphics_2d/simple_runner.spl (helpers) |

All are now in `_binary_override_vars()`. None of them is set in a normal run,
so the daemon hot path is unaffected (verified: none present in the ambient
environment).

Checked and **not** a compounding factor: none of the sixteen uses the inert
bare-`assert` form — all assert through `expect` / `assert_true` / `assert_equal`
(counts 7..234 per file). One, `green_carrier_qemu_spec.spl`, does carry the
self-heal fallback ladder described below, so its override is now delivered but
still not decisive.

Regression coverage extended:
`test/03_system/check/test_daemon_env_override_passthrough_spec.spl` gained an
example that deliberately names **no** variable from the original five, so it
can only pass while the sibling names remain listed.

### The regression coverage for the 2026-08-02 fix had itself never passed

Running the existing passthrough spec before changing anything returned
`2 examples, 2 failures`. The cause is not the daemon at all — it is the same
Simple-interpolation trap this file's own "Fix" section relies on. The fixture
wrote:

```
process_run("/bin/sh", ["-c", "echo shell=[${SIMPLE_TEST_BINARY:-}]"])
```

`{` opens an interpolation inside a Simple text literal, so `${SIMPLE_TEST_BINARY:-}`
is parsed Simple-side and the example dies with ``semantic: variable
`SIMPLE_TEST_BINARY` not found`` **before the shell ever runs**. The
`OVERRIDE_TARGET shell=[…]` line was therefore never printed, `observed_shell()`
was always false, and both examples failed on their `assert_true`. The braces
must be doubled — exactly the escaping that
`guard_backend_parity_spec.spl:99` already documents.

So the spec cited above as "regression coverage" for the 2026-08-02 fix was red
from the moment it landed and could not have been protecting anything. Measured
after doubling the braces: `direct=[OVERRIDE_ALPHA]`, `shell=[OVERRIDE_ALPHA]`,
`1 example, 0 failures`, exit 0.

This is worth separating from the daemon defect: the daemon bug made specs pass
for the wrong reason, whereas this one made the guard fail for the wrong reason.
A red guard that nobody re-ran is the same blind spot in the other direction.

## Still open

The protocol-level fix. `light_request_encode`/`light_request_parse` should
carry the client's environment (a v2 request) so that *any* env-sensitive spec
is correct on the daemon lane, not just the names enumerated above. Until then,
any NEW env var that selects behaviour inside a spec body is silently stale on
the daemon lane unless it is added to `_binary_override_vars()`.

## Results this invalidates

Any past verdict from a spec whose binary override was supposed to select a
non-default binary, when a daemon was already running, was produced against
`bin/simple` regardless of what was requested. In particular the sabotage
control in `c6e30f3a745` — "pointing the override at a deliberately broken
binary and the spec still passed" — was correct as an *observation* but was
misattributed to `env_get`; the shell-based replacement it motivated is
equally dead, so that spec's override remained non-decisive until this fix.

Extending that to the sibling family (2026-08-04): for each of the sixteen files
listed above, **every past verdict produced while a daemon was already alive was
produced against the DEFAULT target, whatever the caller selected.** Concretely,
any prior claim of the following shape is now unsupported and must be re-run:

- *"the CPU-SIMD render-scale contract holds for binary X"* — the run exercised
  `bin/simple`, not X (`cpu_simd_render_scale_contract_spec.spl`).
- *"the QEMU green-carrier / DBFS-boot path was verified against the selected
  guest binary or QEMU build"* — it used the daemon's frozen selection
  (`green_carrier_qemu_spec.spl`, `dbfs_disk_boot_spec.spl`). This one also
  bears on the board-runnable rule: a QEMU claim whose executable selector was
  dead did not test the executable it named.
- *"the direct / device-initiated MMU backends were exercised"* — these two
  names are not backend *pickers*, they are availability gates and oracles
  (`env_get("SIMPLE_MMU_DIRECT_BACKEND") == "1"` guards whether the direct arm
  runs at all, and `gpu_mmu_spec.spl:373` asserts
  `device.probe().available == (env_get("SIMPLE_MMU_DEVICE_INITIATED_BACKEND") == "1")`).
  Frozen, that is worse than a dead picker in one specific way: the *expected
  value* of an assertion came from the stale environment, so the oracle and the
  measurement could disagree for a reason unrelated to the code. A caller who
  enabled a backend may have had the arm silently skipped, and a caller who
  disabled one may have asserted availability against the wrong expectation.
  Same shape in `placement_backends_spec.spl:89`.
- *"the web GPU paint / DrawIR GPU route measurements are per-backend"* — the
  backend selector was frozen, so measurements attributed to different backends
  may all be from one (`web_gpu_paint_device_measured_spec.spl`,
  `web_draw_ir_gpu_route_device_measured_spec.spl`). Any perf *number* attributed
  to a named backend from these two specs should be treated as unattributed.
- *"the GPU-compiler artifact provenance/SHA256 was checked against the supplied
  producer/runtime"* — path and expected-hash were both frozen
  (`native_cli_mode_transport_regression_spec.spl`).
- *"clang/LLVM smoke passed against the `LLVM_BUILD` toolchain"* — it passed
  against whichever build the daemon had (`smoke_clang_spec.spl`).
- *"the hosted-browser pipe perf was measured with the selected browser"*
  (`hosted_browser_process_pipe_perf_spec.spl`), *"devhub mail was exercised
  against the selected mail binary"* (`email_cmd_spec.spl`), *"T32 ran on the
  selected Python/backend"* (`t32_hw_helpers.spl`, both copies), and *"the
  native build target was honoured"* (`compile_targets_env_facade_source_spec.spl`).

The scope limit is worth stating precisely, because it keeps this from being an
over-claim: a verdict is only suspect if the run **set the selector at all**.
Runs that took the default were always testing the default and are unaffected;
and a run that itself started the daemon was correct (run B above). What can no
longer be assumed is that any *particular* historical run fell in either safe
category, because nothing recorded the daemon's identity at the time.

## Second, independent vacuity found during the sweep

Several of the sibling specs also carry a **self-heal fallback ladder**: if the
selected binary's output does not contain the expected marker, they silently
re-run against `src/compiler_rust/target/{release,debug}/simple`. With the
override now genuinely delivered, pointing these at a *nonexistent* binary
still leaves them green, because the ladder swallows the failure. So for these,
the override is delivered but **not decisive** — a broken selected binary
cannot turn them red. Measured (daemon killed before every run, override
pointed at a stub that exits 42):

| spec | override delivered | broken binary turns it red? |
|------|--------------------|------------------------------|
| test/01_unit/compiler/interp/mem_guard_rate_spec.spl | yes | no — ladder masks it |
| test/01_unit/runtime/mem_attr_gate_spec.spl | yes | no — ladder masks it |
| test/03_system/check/doctest_lane_symmetry_contract_spec.spl | yes | yes — 6/6 failed |

The ladders are deliberate (they absorb a deployed binary that predates a newly
added extern), so removing them is a separate decision, but they must not be
mistaken for override coverage.

## Re-verification 2026-08-17 (content check + attempted repro, no code change)

Confirmed by reading current `src/app/test_runner_new/test_runner_client.spl`:
`_binary_override_vars()` (line 466) still exists and is consulted at lines
486 and 494, and `src/app/test_daemon/light_protocol.spl` still has **no**
env field on the wire (`light_request_encode`/`light_request_parse` carry only
header/expiry/path) — matching the doc's own "client-side fixed,
protocol-level fix still open" status exactly.

Attempted to re-run `test/03_system/check/test_daemon_env_override_passthrough_spec.spl`
(the cited regression coverage) as fresh evidence. It did not complete within
budget: `bin/simple test <spec> --no-session-daemon --sequential --timeout 180`
produced `Results: 1 total, 0 passed, 1 failed` with
`SPEC FILE VERDICT: ... timeout=1 reason=child-timeout budget_ms=180000` — the
spec's own body shells out to nested `bin/simple test` invocations, each of
which pays the fixed ~310s daemon-path setup cost documented in
`test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md`, so it can no
longer finish inside a 180s per-file budget. This is INCONCLUSIVE for the
env-override behavior itself (the timeout is the row-3 defect, not a
regression here) — it does not contradict the client-side-fixed verdict, but
the regression spec is currently unable to produce a fresh PASS/FAIL signal on
this host without a longer timeout. **Verdict: ALREADY-FIXED-CLOSED for the
client-side/allowlist fix (content-confirmed); protocol-level fix remains
correctly OPEN. No code change made in this pass.**

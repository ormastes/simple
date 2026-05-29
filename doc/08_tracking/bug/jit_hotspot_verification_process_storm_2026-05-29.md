# JIT Hotspot Verification Process Storm — 2026-05-29

## Status

Fixed for refreshed local artifact.

## Context

While continuing `doc/03_plan/agent_tasks/optimization_plugin_jit_hotspot.md`,
focused verification of hotspot-related tests became unsafe because the host had
runaway `simple` process trees.

Observed evidence:

- `bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean`
  produced no useful output for roughly 90 seconds, then reported
  `Resource temporarily unavailable (os error 11)`.
- Process inspection showed thousands of nested
  `bin/simple test test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl --mode=interpreter --clean`
  processes.
- Additional recursive process chains were observed for:
  - `bin/simple native-build ... build/web_baremetal_size_audit/simple_web_placeholder_native`
  - `bin/simple native-build ... build/web_baremetal_size_audit/simple_render_html_native`
  - `bin/simple test test/system/infra/heavy_work_preflight_spec.spl`
- A stuck `scripts/check-workspace-root-guard.shs audit --staged` process left
  `.git/index.lock` behind through `git check-ignore --stdin`.

## Impact

Hotspot Phase 2 benchmark and test evidence is not trustworthy on this host
until the process storm is fixed or the tests are rerun in a clean environment.
The feature plan must remain open.

## Expected Behavior

Focused test and benchmark commands should run one bounded test process tree and
either complete, fail, or time out with a controlled diagnostic. They must not
recursively spawn unbounded `bin/simple test` or `bin/simple native-build`
processes.

## Reproduction Commands

Do not run these on a loaded host until a process-count guard is in place:

```bash
bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean
bin/simple test test/unit/compiler/mir_opt/general_patterns_backend_recommendation_spec.spl --mode=interpreter --clean
bin/simple test test/system/infra/heavy_work_preflight_spec.spl
scripts/check-web-baremetal-size-audit.shs
```

## Resolution Criteria

- Add a preflight or runner guard that refuses heavy Simple tests when active
  `simple` process count is above a small threshold.
- Fix the recursive spawn path for Simple test/native-build invocation.
- Rerun the hotspot unit specs and `test/perf/compiler/jit_hotspot_plan_bench.spl`
  on a clean host.
- Update `doc/03_plan/agent_tasks/optimization_plugin_jit_hotspot.md` with the
  passing commands and evidence.

## 2026-05-29 Update

Source changes in `src/app/cli/test_entry.spl` and
`src/app/cli/commands/test_batch.spl` add a `SIMPLE_TEST_DEPTH` guard and switch
isolated spec execution from nested `test` to `run`.

Verification with the Rust debug runtime is bounded:

```bash
src/compiler_rust/target/debug/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean --progress none
# PASS: 51 tests; post-run matching process count: 0
```

Before that source-level evidence, the stale checked-in `bin/simple` native
artifact reproduced the process storm for the same hotspot spec and required
killing process group `2929639`. Do not use `bin/simple` for this verification
until it is rebuilt from the guarded source.

## 2026-05-29 Local Artifact Refresh

The ignored local `bin/simple` artifact was refreshed from the verified guarded
runtime and rerun:

```bash
bin/simple test test/unit/compiler/interpreter/tiered_jit_hotspot_spec.spl --mode=interpreter --clean --progress none
# PASS: 51 tests
pgrep -af '/home/ormastes/dev/pub/simple/bin/simple test|src/compiler_rust/target/debug/simple test' | wc -l
# 0
```

The process-storm reproduction no longer occurs on the refreshed local command
path.

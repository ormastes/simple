# Test Runner Layer Expert

## Role

Own layer-specific process knowledge for the **pure-Simple test runner**
(`src/app/test_runner_new/`): the spec-header directive contract, the child-env
setup that every spec inherits, statement-coverage wiring, and the workspace
cleanup tool that shares its lifecycle. This layer is what turns a `*_spec.spl`
file into a child process with a specific environment — most "the spec is
green/red for no reason" reports resolve here, not in the code under test.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)

## Layer Links

- Architecture: [doc/04_architecture](../../../04_architecture/)
- Design: [doc/05_design](../../../05_design/)
- Specs: [doc/06_spec](../../../06_spec/)
- Source: [src/app/test_runner_new](../../../../src/app/test_runner_new/)
- Agent-facing spec-writing process: `.claude/skills/spipe.md`

## Owned source

`src/app/test_runner_new/` — `main.spl`, `test_runner_main.spl`,
`test_runner_single.spl` (single-spec driver: directive parsing, child env,
coverage report), `test_runner_client.spl`, `test_runner_debug_tui.spl`,
`test_db_migrate.spl`, `test_db_perf.spl`, `test_dep_graph.spl`,
`test_result_cache.spl`, `json_wrapper.spl`.

## Public contract: spec-header directives

Exactly **two** `# @…` header directives are parsed by the runner today (both in
`test_runner_single.spl`, both by raw substring match on the file text):

| Directive | Parser | Effect |
|-----------|--------|--------|
| `# @di_test` | `test_runner_single.spl:188` | marks the spec as a DI test |
| `# @exec_limit <N>` | `spec_exec_limit_directive`, `test_runner_single.spl:190` | raises the child's `SIMPLE_EXECUTION_LIMIT` |

Everything else in a spec docstring (`@tag`, `@cover`, …) is consumed by the
docgen/SPipe side, not by this runner.

### `# @exec_limit <N>` — the ONLY way to raise a spec's op cap

**In-process arming is INERT.** `rt_fault_set_execution_limit` called from
inside a spec does nothing, because the driver reads `SIMPLE_EXECUTION_LIMIT`
**once at startup** (`src/compiler_rust/driver/src/cli/init.rs:163`). A spec
therefore cannot raise its own cap; the runner must forward it into the child
env. That forwarding lives in the env setup in `main()`
(`test_runner_single.spl`, ~line 599).

```
# @exec_limit 2000000000
```

- Plain comment line, anywhere in the file. The parser does a raw `find_raw`
  for the literal `"# @exec_limit "`, then reads consecutive ASCII digits.
- Absent, or no digits after the space ⇒ returns 0 ⇒ no directive applied.
- **Raise-only**: if `SIMPLE_EXECUTION_LIMIT` is already set higher in the
  environment, the existing value wins. The directive never lowers the cap.
- Default cap without it is 10M operations.
- Reference consumer, with an in-file doc-comment explaining the why:
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tile_gpu_lane_spec.spl`
  (two 600x400 readback + per-tile checksum passes exceed the default).

Related env the same setup manages: `SIMPLE_TIMEOUT_SECONDS` (raise-only
against the monitor timeout) and `SIMPLE_SYSTEM_TEST` (`1` for paths containing
`/system/` or `/feature/`, else `0`).

## Statement coverage

- Working `SIMPLE_COVERAGE=1` statement coverage landed as `1a6c1e362a5`
  (pure-`.spl` wiring); the instance-method attribution fix is `d905ebdb7aa`.
- Wiring lives in `test_runner_single.spl` (`_cov_report_for_file:494`,
  `_cov_print_report:537`) and `test_runner_client.spl`.
- Run: `SIMPLE_COVERAGE=1 bin/simple test <spec>`.
- Attribution model and its caveats:
  [statement_coverage feature expert](../../feature_expert/statement_coverage/skill.md).
- Known caveat carried by the webrender plan doc: a file can measure ~1%
  despite a green lane exercising it heavily (`dom.spl` under the 38/38 DOM
  lane). Treat low coverage on a green lane as an **attribution** question
  before concluding the lane is vacuous.

## The light daemon clamps `--timeout` at 600s — and env vars do NOT lift it

`LIGHT_REQUEST_MAX_TIMEOUT_MS = 600000` (`src/app/test_daemon/light_protocol.spl:1-2`).
`light_request_timeout_ms_from_seconds` clamps any larger `--timeout` down to it,
so `--timeout 3000` silently becomes 600s. **`SIMPLE_TIMEOUT_SECONDS=0` does not
raise this ceiling** — that env var disables the separate 60s CPU guard, which is
a different limit.

Two distinct limits, two distinct symptoms — do not confuse them:

| limit | where | symptom | knob |
|---|---|---|---|
| CPU guard, ~60s | resource monitor | exit **143** (SIGTERM) at ~62s, message names `SIMPLE_TIMEOUT_SECONDS` | `SIMPLE_TIMEOUT_SECONDS=0` |
| daemon request cap, 600s | `light_protocol.spl:1-2` | `ERROR: test daemon timed out`, or exit 255 + `Process timed out`, **no `Results:` line** | none — see workaround |

A spec whose real runtime exceeds 600s **cannot be verified by a plain
`bin/simple test <spec>`**: it reports a daemon timeout instead of a verdict.
Observed 2026-08-04 on `test/01_unit/os/crypto/x25519mlkem768_pinned_workload_spec.spl`
(~13 min wall). Three attempts produced no verdict line; the run that finally
reported `Results: 8 total, 8 passed, 0 failed` only did so because it was
launched **detached**, so daemon-side execution outlived the client's give-up.

Consequences for measurement:

- A daemon timeout is **not** a failure and **not** a pass. Record it as a
  timeout, exactly like the exit-255 case.
- Do not "fix" such a spec by raising `--timeout`; the clamp ignores you. Either
  run detached and read the log, or reduce the spec's real cost.
- A spec that cannot be run by its normal command is not runnable. File it as a
  concrete todo rather than leaving it as folklore.

## Two ways a fully-passing spec reports FAIL (2026-08-06, both fixed)

Neither involves the spec's own code — both are `src/app/test_runner_new/`
plumbing bugs, and both produce a `FAIL` whose example count doesn't match
any real `✗` assertion:

- **`--no-cache` didn't bypass the session-daemon cache.** Only `--clean`
  did; `--no-cache` was silently a no-op against the daemon's stale-result
  cache, and a cached-failure result copied no diagnostic text into the
  display — so a stale red result could show with nothing explaining it.
  Fixed in `test_runner_main.spl` (`20348690152`).
- **`fn main` collision with an unrelated tool's own entry point.** The lint
  CLI (`src/compiler/90.tools/lint/_LintMain/entry_and_fixes.spl`) used to
  wildcard-re-export a bare `fn main`, which collided with the synthesized
  `fn main` every interpreter-mode spec gets. On collision the wrong `main`
  ran (no args), hit its own usage guard, and printed `Usage: simple_lint
  <file.spl> [options]` into the spec's own output — miscounted by the
  runner as one extra failed example, flipping an all-green spec to `FAIL`.
  Fixed by renaming to `fn lint_main` + an explicit non-wildcard re-export
  list (`1517fbe7b51`).

**Diagnostic:** a `FAIL` with a mismatched example count, or with unrelated
CLI usage/help text interleaved in the log, is this class — re-run with
`--no-session-daemon` and read the full log before assuming a real
regression. Detail: `.claude/skills/spipe.md` §"A `Results:` FAIL can be
harness plumbing, not the spec".

## Adjacent tooling: `simple clean`

`src/app/clean/main.spl` — manual + automatic temp/cache cleanup. Auto mode is
**opt-in via `SIMPLE_AUTO_CLEAN=1`** (`main.spl:254`), runs at `simple build`
start, budget `SIMPLE_CACHE_MAX_GB` (default 20). It is off unless that env var
is set, so it cannot silently delete a session's artifacts.

## Shared working tree: blob-first landing (2026-08-07)

A concurrent session's checkout/reconcile can silently wipe an in-progress
file on this shared working tree — no `git status` trace. Persist each
written file's blob immediately (`git hash-object -w <file>`, record the
SHA), build the landing commit from blob SHAs via a scratch
`update-index --add --cacheinfo` (never re-read the working tree at landing
time), and restore a vanished file with `git cat-file -p <sha> > <path>`. The
three push guards default to a jj/HEAD-relative range that is wrong for a
plumbing commit — invoke them with an explicit `BASE..NEWCOMMIT` range. Full
detail: `.claude/skills/spipe.md` §"Shared working tree: blob-first landing".

## Unstable mode + the `run_all` misreading (2026-08-17)

Contract, rationale and acceptance:
`doc/02_requirements/infra/supervised_test_runner.md` § "Unstable mode".
Per-unit separate process for build AND test, run to the end of both lists,
outcomes `OK/ERROR/CRASHED/TERMINATED/TIMEOUT/NOT_RUN`, default ON for
bootstrap / OFF for interactive with `--unstable` / `--no-unstable`. The
session daemon is not the problem and stays.

**Correction the next agent will otherwise get wrong.** `run_all` is a FILE
SELECTION flag — set by `--all`/`--whole` (`test_runner_args.spl:299,301`) and
`--ci` (`:383`), consumed only at `test_runner_files.spl:328,407,468`. It has
nothing to do with keeping going. Keep-going is `fail_fast`, default `false`
(`test_runner_args.spl:184`), sole effect the break at
`test_runner_main.spl:448`. Each spec is already its own process via
`process_run_bounded` (`test_runner_execute.spl:172`), so "continue past a
crash" was already true on the interpreter lane. The genuine gaps were: no
explicit flag, collapsed outcome classes (`exit_code == -1` is one sentinel for
BOTH timeout and death-by-signal), an unaddressed BUILD side, and no crash
fixture. (Files are under `src/lib/nogc_sync_mut/test_runner/`, not this
layer's `src/app/test_runner_new/`.)

### earlyoom hazard — rc 143/144 is UNVERIFIED, never failed

This host runs earlyoom, which fires at **10% memory with zero swap** and
targets processes named `simple`. A spec killed that way exits 143 (SIGTERM) or
144, indistinguishable at the exit code from a real defect. Rule: **any test
result that cannot rule earlyoom out is INCONCLUSIVE** — not a failure and not
a pass. Disambiguation without a runtime change: the crash fixture writes a
sentinel file immediately before self-crashing; sentinel present + died by
signal = `CRASHED`, sentinel absent = `TERMINATED`/UNVERIFIED. Pairs with the
already-open silent-green defect
(`doc/08_tracking/bug/test_runner_emits_no_result_summary_silent_exit0_2026-08-17.md`):
never accept exit 0 without an explicit `Results:` line.

## Feature experts depending on this layer

- [gpu_offload_check](../../feature_expert/gpu_offload_check/skill.md) — seven
  green GPU-offload lanes; carries the `@exec_limit` and render-budget traps
  together with the evidence map.
- [statement_coverage](../../feature_expert/statement_coverage/skill.md)
- [x25519mlkem768_acceleration](../../feature_expert/x25519mlkem768_acceleration/skill.md) —
  hit the 600s daemon clamp above; also the reference case for scoring the
  verdict line rather than the exit code on crypto evidence specs.
- [browser_engine layer](../browser_engine/skill.md) — the render-budget
  silent-truncation hazard is the sibling trap to `@exec_limit`; a
  long-running renderer spec usually needs BOTH.
- [gpu_remote_lanes](../../feature_expert/gpu_remote_lanes/skill.md) — planned
  `cuda`/`vulkan` composite remote backends; extends the mode extractors in
  `test_executor_composite.spl` AND its duplicate
  `test_executor_composite_parse.spl` (both must change together, plus a seed
  driver parser audit). Design:
  `doc/05_design/runtime/gpu_remote_interpreter_architecture.md`.
- [notebook_lanes](../../feature_expert/notebook_lanes/skill.md) — notebook
  executors validate mode specs through this layer's extractor helpers and
  share lane locks (`src/lib/nogc_sync_mut/notebook/lane_locks.spl`, landed) with the GPU lanes for board/GPU exclusivity.
- [prevention_mocks](../../feature_expert/prevention_mocks/skill.md) — its
  directory-wide scope is blocked specifically by this layer's lack of a
  per-directory config/fixture hook (`find_config_file`,
  `test_runner/test_config.spl:297-302`, cwd-relative parent-walk only).

## Update Rule

When this layer's public contract (directives, child env, coverage output),
source ownership, tests, architecture, or verification requirements change,
update this skill with the new links and handoff notes before committing.

## Update Checklist

- Record any new or removed spec-header directive, with its parser location.
- Record child-env variables the runner sets or forwards, and their raise/lower
  policy.
- Record coverage output changes and attribution caveats.
- Record feature experts that depend on this layer.

Template: `.spipe/spipe/doc/00_llm_process/template/layer_skill.md`

## Profile pinning from `simple.sdn` (WP-4, 2026-08-07)

`resolve_effective_profile` (`src/lib/nogc_sync_mut/test_runner/test_runner_config.spl`)
reads the **canonical SDN indent/colon** form only:

```
lints:
  profile: critical
```

The TOML-ish `[lints]` / `profile = "x"` shape it used to scan for was deleted:
no manifest in the tree ever carried it, so the scanner always returned `""` and
project-level profile pinning did not work at all (aerospace hardening plan
premise 4, `doc/03_plan/language/assurance/aerospace_hardening_plan_2026-08-07.md`).

- Path-taking `read_sdn_lints_profile(path)` is exported so specs can drive it
  from a fixture instead of depending on cwd. Fixtures:
  `test/fixtures/project_sdn_profile/{with_profile,without_profile,legacy_toml}/simple.sdn`.
- The canonical **typed** loader is
  `compiler.driver.project.ProjectContext.load_from_sdn`, which maps
  `project.name`/`source_root`, `features`, `lints.profile` (→ `set_active_profile`)
  and the remaining `lints.*` keys into `lint_overrides` via
  `std.common.sdn.parser`. `src/lib` must NOT import it (upward dependency), and
  executing extra module init in a session that later drives frontend parsing
  triggers `doc/08_tracking/bug/interp_lint_main_then_frontend_dict_to_int_2026-07-28.md`
  — hence the deliberate small duplicate here. Unifying the three readers is WP-3.

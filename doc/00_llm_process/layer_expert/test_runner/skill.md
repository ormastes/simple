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

## Verdict reporting: which line is authoritative (2026-08-04/05)

Three different summary grammars exist, and they are not interchangeable:

| producer | line | source |
|---|---|---|
| `bin/simple test` | `Results: N total, M passed, K failed` | `test_runner_single.spl:225` |
| per top-level `describe` | `N examples, M failures` (ANSI-wrapped, singular `1 failure`) | `src/compiler_rust/driver/src/cli/test_output.rs:164`, `:251` |
| per spec FILE | `SPEC FILE VERDICT: <path> declared>=N executed=N passed=N failed=N dropped=N` | `src/compiler_rust/driver/src/cli/basic.rs:144` (`5b57a79f8ba`) |

- **`tail -1` is wrong.** The per-describe line is printed once per group and the
  file-level failure line goes to **stderr**, so stdout can end on a green count
  from the last group of a failed file (measured: the nine-example
  `trait_scanner_spec.spl` ended stdout `3 examples, 0 failures`).
- **The FILE verdict line deliberately avoids the substrings `examples, ` and
  `failures`** because `test_runner_single.spl:305`
  (`parse_child_example_summary`) **sums every per-describe line it sees** — a
  file-level line in that shape would double every count in the repo. If you add
  any new aggregate line to this layer, keep that constraint.
- `parse_child_example_summary` sums rather than last-wins on purpose: last-wins
  previously let a passing final `describe` erase earlier failures (file summary
  `Failed: 0` + PASS + exit 0 on a red spec).
- `count_real_examples` (`test_runner_single.spl:290`) is the fail-closed
  counter — it counts the runner's own per-example glyphs (`✓`/`✗`) and the
  compiled-mode `... ok` / `... FAILED` suffixes, because the aggregate line
  miscounts a `pending()`-only spec as `1 example, 0 failures`.
- **Strip ANSI before matching anything.** `strip_ansi` lives in
  `src/lib/nogc_sync_mut/test_runner/test_runner_files.spl`. An anchored
  `^[0-9]+ examples` matches nothing against real output; a loose digit scoop
  reads `[32m` as digits and inflates counts ~10×.
- **`declared>=` is a strict lower bound.** `unconditional_example_floor` counts
  only examples reachable through module-level statements and describe/context
  bodies; `if cfg:` / `for x in xs:` generation, `it_behaves_like`, and
  skip/pending contribute zero. Only `executed < declared` is reported as a
  drop, which cannot happen without one — so this check cannot cry wolf.

## Discovery: two paths, and the frozen legacy mirror

`src/lib/nogc_sync_mut/test_runner/test_runner_files.spl` owns discovery.

- **`test/unit/` is a FROZEN legacy mirror** of `test/01_unit/`, excluded from
  **directory** discovery in `acea4ec4c1c`. Nothing is deleted and an explicit
  path under `test/unit/` still runs — the same policy as the existing
  `/fuzz/`, `/chaos/`, `/deploy/`, `/security/` filters. Rationale recorded in
  the source comment (`test_runner_files.spl:25-45`): 874 shared pairs differ,
  sampling found ~33% with differing example counts, and specs exist that are
  GREEN under `01_unit` and RED under `unit`. Predicates:
  `is_legacy_mirror_path` (anchored on a whole path segment, so an unrelated
  `.../mytest/unit/` is not swept in) and `targets_legacy_mirror`.
- **Both discovery paths must apply every filter.** `discover_test_files`
  defaults to `discover_test_files_fast`, which filters manifest entries in
  memory and **never reaches** `discover_test_files_slow`'s walk — so guarding
  only the walk leaves a filter inert on every warm-manifest run. This is the
  single most common way a discovery change lands with no effect.
- **`test/` holds 14 symlinks into `src/`** (measured at `c605154975e` via
  `git ls-tree -r <sha> test/ | /usr/bin/grep '^120000'`). A follow-links walk
  made 27% of one census's "test files" `src/` aliases. Walk without `-L` and
  dedupe by realpath. Three of the 14
  (`test/03_system/feature/lib/{app,compiler,lib}`) are **dangling**, so a
  `[ -d "$(readlink -f …)" ]` filter counts only 11 — count the `120000` blobs.

## Adjacent tooling: `simple clean`

`src/app/clean/main.spl` — manual + automatic temp/cache cleanup. Auto mode is
**opt-in via `SIMPLE_AUTO_CLEAN=1`** (`main.spl:254`), runs at `simple build`
start, budget `SIMPLE_CACHE_MAX_GB` (default 20). It is off unless that env var
is set, so it cannot silently delete a session's artifacts.

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

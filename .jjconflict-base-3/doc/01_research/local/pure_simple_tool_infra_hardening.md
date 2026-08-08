<!-- codex-research -->
# Pure-Simple tool and infrastructure hardening: local research

Date: 2026-07-16

## Scope and method

This audit covers the production CLI, test runner, test daemon, checker, lint,
formatter, fixer, duplicate checker, SPipe/doc generation, MCP/LSP wrappers, and
the bootstrap/deployment boundary. Three read-only sidecars separately reviewed
test/compiler paths, lint/duplication paths, and docs/wrappers. The primary
Codex model reconciled their findings. Vendored code was excluded.

The worktree contains unrelated concurrent changes, including test-runner and
bootstrap work. This audit did not edit or claim ownership of those files.

## Authoritative runtime status

`bin/simple` resolves to `bin/release/x86_64-unknown-linux-gnu/simple`, but the
binary identifies itself as the Rust bootstrap seed. Therefore no command result
from that artifact proves pure-Simple behavior. Artifact-only probes found:

| Probe | Current result | Interpretation |
|---|---|---|
| `simple --version` | Rust bootstrap-seed warning | BLOCKER: deployed runtime provenance is invalid |
| `test --help` | exits 1 | Not usable as pure-Simple evidence |
| `lint`, `fmt`, `check --help` | `unknown extern function: rt_cli_arg_count` | Stale/degraded artifact |
| `duplicate-check --help` | treated as a source filename | Command absent from deployed artifact |

The first hardening gate must fail closed when the release-path binary is a seed.

## Important tool status

| Tool | Source owner / route | Status | Confirmed problem | Minimal solution |
|---|---|---|---|---|
| CLI dispatch | `src/app/cli/dispatch*` | Partial | Table has 81 entries while reported totals are hard-coded to 53 | Derive counts from the command table |
| `test` | `src/app/test_runner_new/main.spl` plus runtime-family test-runner libraries | Blocked | Production implementation still exposes Rust SFFI routing; sibling top-level `describe` blocks have a tracked hollow-green bug | Deploy pure-Simple runner, then add red/empty/multi-describe contract probes |
| Test runner resources | runner lifecycle/resource governor | Open defects | Parent RSS growth and nested-runner timeout are tracked | Bound/re-exec batches and retain one timeout/RSS acceptance test |
| Test daemon | `src/app/test_daemon/` | Source present | Pure-Simple runtime not proven | Validate status/run/clean/stop only after provenance gate |
| `check` | CLI check entry and compiler driver | Blocked | Deployed artifact lacks `rt_cli_arg_count`; global flag check timeout remains tracked | Fix/redeploy shared CLI ABI, then add one deadline-bound probe |
| `lint` | `src/app/io/cli_lint_commands.spl`, `_CliCommands/run_commands.spl`, compiler lint suite | Incorrect/duplicated | Two divergent handlers; suppression code strips spaces then searches for spaces and suppresses at file scope | Reuse compiler annotation parsing and one shared handler |
| `fmt` / `fix` | same two CLI handler surfaces | Duplicated | Behavior can drift; fast wrapper executes raw source worker | Keep one implementation; wrappers adapt arguments or execute a cached artifact |
| `duplicate-check` | `src/compiler/90.tools/duplicate_check/` | Security + evidence failure | CLI path/excludes enter shell commands; benchmark specs are placeholder-only and duplicated under `test/perf` and `test/05_perf` | Use `dir_walk`/`file_read`; retain one real benchmark spec |
| SPipe/docgen | CLI/SPipe surfaces | Partial | Broad repository still contains placeholder passes; feature lacks a production-path system-spec/manual pair | Make placeholder audit release-blocking and generate the manual from the executable spec |
| MCP/LSP wrappers | `bin/*mcp*`, `src/app/mcp`, `src/app/simple_lsp_mcp` | Degraded | Unix LSP wrapper defaults SMF execution through the Rust seed; Windows launcher gives Rust paths precedence | Prefer verified cached pure-Simple artifacts and fail closed |
| Bootstrap/deploy | `scripts/bootstrap/bootstrap-from-scratch.sh` and release links | Blocking | Release path can contain a seed while looking production-like | Atomic deploy with provenance probe before symlink swap |

## Root-cause evidence

1. `src/compiler/90.tools/duplicate_check/detector_files.spl:12` interpolates a
   CLI path into `find`. `doc_extractor.spl:32,116,133` similarly interpolates
   file paths and exclude patterns into `cat`/`find`/`awk`. Existing
   `std.nogc_sync_mut.io.dir_walk` and `file_read` cover the required operations.
2. `src/app/io/cli_lint_commands.spl:11-16` compacts whitespace and then checks
   patterns containing whitespace. This cannot correctly parse multi-name
   annotations and duplicates the compiler's lint configuration logic.
3. `src/app/io/cli_lint_commands.spl` and
   `src/app/io/_CliCommands/run_commands.spl` independently implement lint,
   format, and fix behavior and already run different repository gates.
4. `test/05_perf/duplicate_check_benchmark_spec.spl` has five
   `expect(true).to_equal(true)` assertions; the file is duplicated under
   `test/perf/`.
5. `src/app/cli/lint_entry.spl:60-64` invokes `bin/simple run` on a raw source
   worker, violating the cached-production-artifact rule.
6. `src/app/test_runner_new/test_runner_single.spl:14,226-235` directly owns
   `rt_env_set` instead of using the app IO facade.
7. Existing tracked defects include runner parent memory growth, nested-runner
   timeout, sibling top-level `describe` loss, global flag checker timeout,
   native LSP/MCP argument/deadlock failures, and recursive `gen-lean` dispatch.

## Existing related artifacts

`pure_simple_cli_completeness` already has research, requirements, architecture,
and detail design, but it does not cover this broader hardening scope and has no
feature-named system test, generated manual, or system-test plan. Its four CLI
requirements should be treated as inputs, not proof that the production route is
complete.

## Recommended work order

1. Provenance and atomic deployment gate.
2. Production-path command matrix with explicit exit semantics.
3. Hollow-green runner fixes and real runner resource evidence.
4. Duplicate-check shell removal and real canonical benchmark.
5. Lint/fmt/fix consolidation and annotation correctness.
6. Pure-Simple cached MCP/LSP/Windows wrapper routing.

## Implementation-ready root fixes

### Duplicate checker

- Replace `shell_output("find ...")` in `detector_files.spl` with
  `std.nogc_sync_mut.io.dir_ops.dir_walk_native`, then keep only `.spl` files
  and apply the existing exclusion matcher.
- Remove the fallback shell `cat`; `file_read` already handles arbitrary paths.
- Replace the batch `find | xargs | awk` path with `collect_files` plus
  `extract_docs_from_file`. This is the existing Simple implementation and
  removes path, exclude-pattern, and generated-script quoting surfaces at once.
- Regression fixtures must include semicolons and apostrophes in real paths and
  assert that no sentinel command executes.

### Lint

- Delete `file_allows_lint` substring parsing.
- Reuse `LintConfig.apply_file_attributes` through `Linter.lint_source`, which
  already copies configuration, parses annotations, filters results, and applies
  severity.
- Prove a multi-name `@allow(todo_format, primitive_api)` suppresses only the
  annotated scope through the production handler.

### Test runner

The current source sums multiple summary lines but does not prove execution of
multiple sibling top-level `describe` blocks. `std.spec.describe` emits no
per-describe summary, and the wrapper only rejects a global executed count of
zero. A file where the last sibling runs can therefore still pass the zero-test
guard. Closure requires a production-path fixture with a failing first sibling
and passing second sibling, expected count two, and nonzero process exit.

Two additional runner root causes are confirmed statically:

- `make_result_from_output` only converts a nonzero child exit into an error
  when `passed == 0`. A child that prints a green summary and then exits nonzero
  can remain successful. `test_runner_single` similarly replaces the initial
  process-code failure with parsed zero failures. Nonzero child exit must always
  make the file non-OK; parsing may add detail, never erase process failure.
- Nested `simple test` calls submit to the same single-threaded light daemon that
  is blocked waiting for the outer test. Daemon-launched children need an
  environment marker, and the client must route nested runs directly through
  the no-daemon path.

The main CLI currently collapses pass, assertion failure, empty discovery,
usage error, internal error, and timeout into `0`/`1`. The chosen requirements
should assign stable exit classes at the CLI boundary while keeping internal
result types descriptive.

### Provenance and wrappers

- Reuse `candidate_frontend_admission.shs`; do not invent a second provenance
  detector. `scripts/setup/setup.shs` must run that admission before linking a
  release candidate.
- Preserve the bootstrap seed as an explicitly named delegate until remaining
  dependencies are removed, but never accept it as the production runtime.
- Make Unix LSP native-first with a real correlated `lsp_symbols` probe; source
  fallback may use only a validated pure-Simple runtime.
- Route `config/mcp/install.shs` through the checked wrapper.
- Align generated and checked-in MCP default mode, then assert the default in
  `check-mcp-wrapper-contract.shs`.
- Windows launchers require the same policy, but their files are currently
  owned by another dirty lane and must not be edited without coordination.

# Full CLI sanity oracle source binding maintenance

Status: source review only; runtime qualification pending. Do not use this
receipt as full CLI, bootstrap, test-suite, or release admission.

## Exact source review

Base: release `8303221132a`; original oracle creation:
`e53410f3c1863d30e2489c6694f7bb25628fbf0f`.
The original commit bytes reproduce both old registry digests. Reviewing the
complete old-to-base diff of the two owners found these changes:

- `src/app/cli/_CliMain/main_and_help.spl` accepts the committed `llvm`
  composition alongside `llvm-cranelift`. An unset requested policy now uses
  the selected binary policy; explicit mismatch and unsupported policy still
  fail. Version, evaluation, check, and test dispatch are unchanged.
- `src/app/io/cli_ops.spl` removes Rust seed-only test/compile dispatch externs,
  the unused process-argument test wrapper, and its compile re-export. Arg/file
  helper imports move from the broad SFFI CLI owner to `cli_args`. The explicit
  `SIMPLE_NO_BOOTSTRAP_DELEGATE=1` checks and interpreter delegation rules are
  unchanged.

Only these two normalized source digests change in `reviewed-sources.tsv`:

| Owner | Reviewed digest |
|---|---|
| `main_and_help.spl` | `820f7e0956764cd6c6927543561f55a2401d817c4bd49ca062f85b4a32c63366` |
| `cli_ops.spl` | `ec0358e6aa5ee2b2bb42641a2f8bb6a6978b2805f71e3025b4184086df74c11d` |

## Preserved evidence contract

The other three full CLI bindings, expected stdout/stderr, role selection,
version/evaluation probes, five-second process owner, environment suppression,
binary digest checks, and `whole_tests_qualified=0` are unchanged. With
bootstrap delegation suppressed, `cli_run_code` stages a private snippet and
calls `interpret_file` in process. A version-only result cannot qualify the
full CLI role. The two probes do not qualify check/test execution.

## Verification limits

The source guard validates all five normalized bindings and patch scope;
`git diff --check` checks patch whitespace. The existing native C fixture oracle controls passed all eight cases: good
output, wrong version, empty evaluation placeholder, extra stdout, stderr,
wrong exit, timeout, and source drift rejection. Evidence is retained at
`/home/yoon/dev/simple-full-cli-oracle-controls-20261011/results.tsv`. Sparse
setup initially lacked the process-owner resource directory; the complete run
used the canonical process owner after its dependencies were checked out.
These are oracle tooling controls, not a Simple runtime or Phase 4 product
PASS. No Simple native build, SSpec, or product runtime was executed. Before
admission, run both probes against the exact newly constructed pure-Simple
full CLI. Check/test
execution, core/MCP/LSP gates, and bootstrap qualification remain separate.
The frozen release candidate is not edited by this maintenance worktree.

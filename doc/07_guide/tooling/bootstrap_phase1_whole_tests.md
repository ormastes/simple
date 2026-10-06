# Phase 1 configured whole tests

The candidate callback scripts/bootstrap/phase1-whole-tests.py runs the configured
whole tests using an explicitly pinned Phase 1 seed. It must be invoked as an
owned task in the shared 80-job manager, with 20 jobs allocated. It creates no
detached owner or second resource scheduler. Automatic from-scratch graph wiring
is not yet implemented. Phase 2 product preparation and compilation may proceed
concurrently; only product test execution waits for Phase 1 terminal completion.
A Phase 1 failure remains failure but does not cancel later authorized test runs.

The pinned seed executes the repository's default Simple test runner with
`test --whole --parallel --max-workers=20 --unstable --mode=interpreter --format=json`.
The legacy `SIMPLE_TEST_RUNNER_RUST` override is removed from the child environment:
that runner reads legacy TOML and does not consume the current SDN configuration.
`SIMPLE_BINARY` and `SIMPLE_RUNTIME` bind test and doctest children to the same seed.

Existing policy remains authoritative:

- `config/simple.test.sdn` enables specification, SPL-comment, and documentation tests.
- `config/sdoctest.sdn` selects Markdown sources, ignores, and environments.
- `std.test_runner.test_runner_files` applies platform tags, execution-mode and
  architecture directory rules, `.skip`/`@pending`, and explicit environment opt-ins.
- `std.spec.condition` evaluates runtime, platform, hardware, and feature skips.

No manual Rust support list replaces these selectors. Unsupported environments
remain skipped, failed runner startup remains infrastructure failure, and a
failed assertion remains a failure. `--unstable` continues the configured list.
No `--clean` or `--force-rebuild` is passed; the runner retains compatible caches.
Use a private writable source copy for diagnostics because test documentation and
test databases are generated during execution.

Each fresh attempt retains the seed/configuration hashes, command, stdout,
stderr, process exit, elapsed time and combined runner summary. JSON output is
one compact line (`test_runner_output.spl:combined_test_run_json`, emitted by
`test_runner_main.spl`). Extraction streams the log and rejects lines exceeding
32 MiB. Crashes, missing categories, duplicate summaries, zero executed assertions,
invalid counters and inconsistent file totals cannot become PASS.

The current JSON schema does **not** expose discovered/excluded/aborted inventory
totals. The receipt therefore explicitly marks overall inventory coverage
`NOT_PROVEN`; successful reported assertions do not prove whole-repository
coverage. Phase 1 results are distinct from the six Phase 2 subsystem products.
Later phases may continue after Phase 1 failure, preserving its failed receipt.
Full bootstrap qualification must retain that failure and require independent
inventory coverage; this callback alone is not a release admission.

The six-product managed graph and its terminal matrix gate are separate work:
compiler/interpreter/loader for LLVM and Cranelift need authentic generated-source
authority, native enumeration and runtime receipts. Diagnostic smoke binaries
cannot substitute for those products.

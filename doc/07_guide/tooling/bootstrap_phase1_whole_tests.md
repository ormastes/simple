# Phase 1 configured whole tests

`scripts/bootstrap/phase1-whole-tests.py` is the current Phase 1 callback
candidate. It runs the configured whole-test command with the pinned Phase 1
seed. Treat it as diagnostic until a fresh, source-bound Phase 1 tuple has been
qualified and its complete evidence reviewed. A successful test summary alone
does not establish complete repository inventory coverage.

## Current candidate and known limits

- The callback now requests the supported human-readable output explicitly
  (`--format=text`) and parses it as bounded diagnostic text. Its first attempt
  used the retired `--json` option and failed before tests ran. Do not describe
  JSON output as the current contract.
- Two distinct public SDN gates remain open: current providers do not
  implement the required `ProcessObservationV4` process-group retirement
  contract, and the whole aggregate is bounded to 1 MiB. Do not bypass either
  guard. The text route is only a diagnostic
  workaround, with bounded output and incomplete coverage proof.
- On 2026-10-27, five parser unit checks passed, but directory calibration
  failed before assertions: the old seed lacks `rt_io_file_open_read`, and the
  structured BDD guard rejects the fixture. This is an unqualified
  calibration, not a parser or whole-run PASS; parser review remains open.
- The human summary has three independent result categories: spec files,
  configured SPL doctests, and Markdown SDoctests. Preserve each category,
  every per-file verdict, declared/executed/pass/fail/skip counts, and dropped
  work. A dropped row, missing or duplicate summary, zero executed work,
  timeout, or inconsistent counters is not PASS. Retain discovered, excluded,
  and aborted inventory accounting; overall inventory coverage remains
  **NOT PROVEN** until independently reconciled.

Do not replace configured selectors with a hand-maintained Rust support list.
The legacy `SIMPLE_TEST_RUNNER_RUST` override reads legacy TOML rather than the
current SDN configuration; remove it from the child environment. Preserve
configured mode/platform/environment selectors and report skips separately
from failures and executed passes.

The configured inventory still comes from `config/simple.test.sdn`,
`config/sdoctest.sdn`, `std.test_runner.test_runner_files`, and
`std.spec.condition`. These own enabled spec/SPL-comment/doc tests, Markdown
source selection, platform/mode/architecture rules, pending and explicit
environment opt-ins, plus runtime/platform/hardware/feature skips. The seed,
`SIMPLE_BINARY`, and `SIMPLE_RUNTIME` must bind test and doctest children to the
same pinned binary. The callback invokes:

```text
test --whole --parallel --max-workers=<jobs> --worker-memory-mb=<MiB> \
  --unstable --mode=interpreter --format=text
```

`--jobs` is admitted in 1..128 and defaults to 20, while
worker-memory defaults to 0 (disabled). The FreeBSD 20-worker lane explicitly
requests 20480 MiB without changing CPU concurrency.

## Admission and resource rules

Run only as an owned task under the shared resource manager with a single
explicit admitted job count. The worker argv, `SIMPLE_TEST_JOBS`, and request
receipt must use the same count. The independent worker-memory budget defaults
to disabled; on unsupported hosts a positive budget must be rejected before
workers spawn. This is an admission throttle, not an OS memory limit. Include
worker budget, parent, and observer headroom in the outer RSS watchdog. Use the
canonical resource guard at 7200 seconds for this campaign; this is not a
universal timeout contract.

Do not repurpose `HOME` to redirect state. Keep the test database and writable
diagnostic source copy isolated from concurrent lanes. Preserve compatible
caches; do not add clean/force-rebuild flags to manufacture a result.

## Fresh Phase 1 refresh

When a refreshed seed is required, use the reviewed canonical
`--full-bootstrap --stop-after-seed` route. It exits before Phase 2. A usable
candidate needs the full new Phase 1 tuple, a candidate isolated from prior
outputs, and the shared computed cache. Do not infer qualification from a seed
binary already on disk or from a previous source tuple. No build or test may be
reported PASS until its command, source/seed identities, logs, exit status,
per-file evidence, and required controls have actually been observed.
The nested disk preflight for this canonical refresh is 20 GiB; do not use the
wrapper's older 10-GiB threshold or override the floor. This refresh requirement
does not change the standalone callback's disk policy.

## Phase boundary

Phase 1 failures remain failures unless an exact, reviewed capability rule
justifies a Phase 1 skip. Keep required later-mode rows open and preserve their
resume command; blocked, skipped, or not-run work is never a pass. Source fix
`5ccb` has an activation gap in pinned seed `59de`; the affected case remains
failed on that artifact and is not a skip. The current campaign directs Phase 2
to begin only after Phase 1 cleanup. This callback does not admit Phase 2,
native bootstrap, or release qualification.

The six-product managed bootstrap graph and terminal matrix gate are separate
from Phase 1 whole tests. LLVM and Cranelift compiler/interpreter/loader
products require generated-source authority, native enumeration, and runtime
receipts; diagnostic smoke binaries cannot substitute.

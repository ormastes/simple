# Bootstrap CI default stopped independent work

The shell bootstrap policy and pure compiler policy treated CI=true/1 as an implicit fail-fast request. Local runs already collected independent failures. This differed from the requested default: attempt independent modules/products/tests to completion and preserve every failure.

Both owners now default to collect-all. Explicit SIMPLE_COMPILE_FAIL_FAST=0/1 and ordered --keep-going/--fail-fast options retain precedence. The ci_value argument remains for caller compatibility. Authority, cancellation, containment and invalid-receipt aborts are unchanged.

Existing manager scheduling continues qualified compiler failures and retains lineage-bound per-job cache roots. The host immutable CAS helper is enabled by bootstrap-from-scratch; no arbitrary mutable cache is shared across producer/phase/source identities. This change does not invalidate or delete compatible caches and does not claim that every entrypoint shares a frontend CAS.

Validation: check-bootstrap-keep-going-policy.shs passed, including actual production scheduling, aggregate FAIL retention, explicit fail-fast, child policy, compatible cache retention and invalid admission rejection. check-bootstrap-phase4-module-collection.shs passed its changed policy/cache cases, but the overall test failed at the existing symlink fixture on Windows Git Bash (ln -s created a regular copy); POSIX executable-bit verification was also unsupported. Do not count that complete test as PASS. Logs are in the runtime packet reviewed-source-integration/default-*.log.

The native fixture test/fixtures/compiler/compile_failure_policy/main.spl asserts defaults, environment precedence and both CLI option orders for five CI spellings. It has not been compiled/run. Adaptive crash recovery is separate from ordinary failure continuation; no unlimited retries or admission bypass is introduced here.

The independent SMF scheduler, CLI guard, membership predicate, epoch identity validator, and summary encoder/decoder now agree on an 80-worker maximum (previously 64). A shell regression launched all 80 callback partitions and rejected 81 before spawn: PASS. Native codec boundary and round-trip assertions were added, but remain unexecuted.

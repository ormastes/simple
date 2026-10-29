# Scenario artifact directory components exceed filesystem limits

Status: artifact owner correction verified; arena/API failures and output-parser
group attribution remain OPEN.

The explicit Rust-seed diagnostic run of `domain_arena_v1_spec.spl` reported
11 passed and 3 failed, then warned that scenario manifest writing failed with
`File name too long`. The Rust driver builds a directory component from the
complete group and scenario text without a bound. Captured MCI ledger output
was parsed as the last scenario's group, producing a component well over 255
bytes. Arbitrarily long legitimate scenario names hit the same defect.

Owner: `src/compiler_rust/driver/src/cli/test_runner/scenario_artifacts.rs`.
The pure-Simple runner has no matching scenario-directory manifest writer in
the inspected source; no shared pure runner vulnerability is established.
The Rust output parser's group heuristic is a separate issue. Manifest output
is a warning, not the cause of the three failing arena scenarios.

Existing `build/test-artifacts/01_unit/lib/nogc_sync_mut/mission_critical/domain_arena_v1/combined.log`
identifies the actual failures:

- `isolates fixed bytes, rolls back staged bytes, and publishes committed bytes`
  (spec line 155): `DomainArenaV1.write_byte` is missing at line 165.
- `rejects forged subspans, wrong domain/generation, and capacity drift`
  (line 191): the same missing operation at line 205.
- `rejects malformed relaxed profiles before cursor mutation` (line 309):
  `DOMAIN_ARENA_V1_MAX_QUOTA_BYTES` is missing at line 325.

The current arena owns quota/generation accounting but contains no byte backing,
`write_byte`, `read_byte`, or committed-byte hash operation. No equivalent
production API was found; these tests require missing byte-storage behavior,
not a caller rename. The V2 spec imports an absent `domain_arena_v2` module and
its stored diagnostic reports that import failure. Assertions and arena
semantics remain unchanged.

Correction: retain short artifact names, bound long ASCII slugs to
180 bytes, and append a SHA-256 digest of unambiguous original group/name
fields so shared prefixes remain distinct. Full names stay in the manifest.
Tests must create actual directories for oversized names and cover shared
prefixes, Unicode, determinism, and existing short-path compatibility.

The exact Rust owner module's eight tests ran in an isolated native Cargo
harness with the same four-field `IndividualTestResult` shape and its existing
`sha2`/`tempfile` dependencies. Before the fix, five tests passed and the three
new tests failed; the filesystem test reproduced errno 63. After the fix,
all eight passed, exit 0. This is focused owner evidence, not a rebuilt full
driver, native Simple test verdict, or repaired arena suite.

- Red log: `/private/tmp/astra-scenario-artifact-red.log`, SHA-256
  `f87bbabfeab06669ae352a967506dcfcc332440fad4b9c32e4f07ca9590bca2d`.
- Green log: `/private/tmp/astra-scenario-artifact-green.log`, SHA-256
  `25365177a7bc33b32e9a80c9a9bd4e4854729686476d1da3bc82b54fe3c3e132`.
- Harness: `/private/tmp/astra-scenario-artifact-tests`; one-job offline Cargo
  execution uses `#[path]` to compile the actual repository module.

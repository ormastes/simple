# SimpleOS guest toolchain wrapper — host-fixture manual

Source: `test/03_system/os/simpleos_guest_toolchain_wrapper_spec.spl`

Status: source/manual current; pure-Simple Stage-4 execution, `spipe-docgen`,
and seven-score `sspec-maintain` evidence remain blocked by B-HOST-CLI.
Stubs: 0. Scenarios: 3 active, 0 skipped, 0 pending.

## Purpose and audience

This manual is for implementers and reviewers validating the production
dispatcher `scripts/simpleos_guest_toolchain_wrapper.shs`. The spec runs that
wrapper against isolated host fixtures and proves routing, target reporting,
stable guest paths, and fail-closed no-host-fallback behavior.

This is `host-fixture` evidence. It does **not** prove that clang, lld, Simple,
or another tool ran inside SimpleOS; it cannot close B-IMAGE,
B-DESKTOP-LIVE, or the umbrella deployment acceptance scenario.

## Preconditions

- Repository root is the current working directory.
- `/bin/sh`, `mktemp`, `grep`, and symlink support are available.
- An admitted pure-Simple Stage-4 test runner is selected. The Rust seed and
  bootstrap-only Stage 2 are not admissible evidence.
- The production wrapper exists at
  `scripts/simpleos_guest_toolchain_wrapper.shs`.

## Operator workflow

1. Run the executable SSpec once with the admitted pure-Simple runner.
2. Require all three examples to execute and the test process to exit zero.
3. Retain the runner path/SHA-256 and complete stdout/stderr log.
4. Run `spipe-docgen` and require `0 stubs`, then run `sspec-maintain scan` and
   review all seven scores independently.
5. Do not promote this result to guest or desktop evidence; run the canonical
   live deployment spec for that claim.

## Scenario 1 — LLVM wrapper routing

Visible steps:

1. Create an isolated guest-wrapper fixture.
2. Query the production clang wrapper status and target.
3. Forward compile and link operations to the staged LLVM payloads.

The scenario requires `lane=x86_64-simpleos`, `mode=native-wrapper`,
`status=guest-exec`, the exact target triple, and exact forwarded clang/lld
arguments. Any nonzero wrapper result fails the example.

## Scenario 2 — CMake and Ninja routing

Visible steps:

1. Create an isolated configure-wrapper fixture.
2. Query production CMake wrapper capabilities.
3. Generate Ninja commands with stable guest tool paths.
4. Forward Ninja execution to the staged payload.

The scenario requires report-and-gate capability output, generated references
to `/usr/bin/clang` and `/usr/bin/ld.lld`, and exact Ninja forwarding. Missing
or rewritten paths fail closed.

## Scenario 3 — unsupported Rust operations

Visible steps:

1. Create an isolated report-and-gate wrapper fixture.
2. Query the production Rust wrapper discovery surface.
3. Reject unsupported Rust compilation without host fallback.
4. Reject unsupported Cargo builds without host fallback.

Discovery must report the SimpleOS lane and target libdir. Build operations
must return rc=1 and contain `no host fallback`; a host compiler success is a
test failure.

## Traceability

| Requirement | Coverage | Claim boundary |
|---|---|---|
| REQ-007 | All three scenarios reject fixed-command/host-fallback promotion | Host wrapper policy only |
| NFR-002 | Nonzero/missing status and unsupported operations fail closed | Host wrapper policy only |
| REQ-003 / REQ-005 | Not satisfied here | Require the live guest deployment spec |

## Evidence and provenance

The executable oracle is the tracked production wrapper, not a duplicate
decision function in the spec. Fixture payload programs only expose their
received arguments; they are deliberately not accepted as target binaries.
Record the spec SHA-256, production-wrapper SHA-256, runner SHA-256, command,
exit code, stdout, and stderr for an admitted execution.

<details>
<summary>Executable SSpec flow</summary>

```simple
describe "SimpleOS guest toolchain wrapper":
    it "should report clang guest status and forward supported LLVM operations":
        step("Create an isolated guest-wrapper fixture")
        step("Query the production clang wrapper status and target")
        step("Forward compile and link operations to the staged LLVM payloads")

    it "should expose the supported CMake and Ninja configure lane":
        step("Create an isolated configure-wrapper fixture")
        step("Query production CMake wrapper capabilities")
        step("Generate Ninja commands with stable guest tool paths")
        step("Forward Ninja execution to the staged payload")

    it "should expose Rust discovery and reject unsupported build operations":
        step("Create an isolated report-and-gate wrapper fixture")
        step("Query the production Rust wrapper discovery surface")
        step("Reject unsupported Rust compilation without host fallback")
        step("Reject unsupported Cargo builds without host fallback")
```

The complete reproducible source, including fixture construction and every
assertion, is the Source path above; this folded view intentionally shows the
operator-visible flow.

</details>

## Compatibility and limitations

- The fixture requires a POSIX host and does not run under SimpleOS.
- The Rust wrapper is intentionally report-and-gate; this manual does not claim
  a target-native Rust compiler.
- An unavailable admitted Stage-4 runner is `TEST_BLOCKED`, not a skipped or
  passing scenario.
- Full acceptance remains
  `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`.

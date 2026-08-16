# SimpleOS compiler and libc source contract — operator manual

Source: `test/03_system/os/os_compiler_bootstrap_spec.spl`

Status: source/manual current; pure-Simple Stage-4 execution, `spipe-docgen`,
and seven-score `sspec-maintain` evidence remain blocked by B-HOST-CLI.
Stubs: 0. Scenarios: 4 active, 0 skipped, 0 pending.

## Purpose and claim boundary

This `source-contract` spec preserves the useful inventory checks from the
historical bootstrap scenario while removing false acceptance signals. It
checks maintained libc, LLVM/Rust port, and SimpleOS integration owners. It
does not build or execute a compiler and cannot prove bootstrap convergence,
image admission, guest execution, or desktop readiness.

The spec deliberately does not check for the Rust seed, `bin/simple`, or the
Rust compiler target registry. Their presence is not pure-Simple self-host or
SimpleOS release evidence.

## Preconditions

- Run from the repository root with an admitted pure-Simple Stage-4 runner.
- The source checkout is complete; generated build output is not required.
- Treat a green result only as source-layout evidence.

## Operator workflow

1. Run the executable SSpec once with the admitted runner.
2. Require all four examples to execute and exit zero.
3. If a path moved intentionally, update its production owner and this source
   contract together; do not add an alternate compatibility copy.
4. Retain the spec and runner SHA-256 plus stdout/stderr.
5. Generate the manual with `0 stubs` and inspect all seven `sspec-maintain`
   scores when Stage 4 is available.

## Scenarios

1. `step("Inspect the maintained SimpleOS libc build and headers")`
   checks the Makefile and public header surface.
2. `step("Inspect the maintained SimpleOS libc implementation owners")`
   checks the fourteen maintained libc implementation units.
3. `step("Inspect the maintained cross-toolchain port owners")`
   checks LLVM and Rust port build/configuration sources without treating a
   host or seed compiler as execution evidence.
4. `step("Inspect the production SimpleOS build and acceptance owners")`
   checks the native-build configuration and the three canonical supporting,
   image-admission, and live-guest SSpec owners.

## Traceability

| Surface | Coverage | Claim boundary |
|---|---|---|
| SimpleOS libc | Build/header/implementation paths exist | Source layout only |
| LLVM and Rust ports | Maintained build/config/example paths exist | Source layout only |
| Simple payload integration | Production build/config/spec owners exist | Source layout only |
| REQ-003..REQ-007 | Not satisfied here | Require production image/live scenarios |

## Evidence and provenance

The oracle is repository path presence. Record the checkout commit, spec
SHA-256, runner path/SHA-256, command, exit code, stdout, and stderr. Do not
combine this evidence with historical build artifacts or promote it to a
runtime claim.

<details>
<summary>Executable SSpec flow</summary>

```simple
describe "SimpleOS compiler and libc source contract":
    it "should retain the libc build and header surface":
        step("Inspect the maintained SimpleOS libc build and headers")
    it "should retain the libc implementation surface":
        step("Inspect the maintained SimpleOS libc implementation owners")
    it "should retain the LLVM and Rust port configuration surfaces":
        step("Inspect the maintained cross-toolchain port owners")
    it "should retain the production SimpleOS integration owners":
        step("Inspect the production SimpleOS build and acceptance owners")
```

The complete reproducible source and assertions are at the Source path above.

</details>

## Compatibility and limitations

- Generated sysroots, build outputs, and deployed binaries are intentionally
  outside this source-contract scenario.
- A missing admitted Stage-4 runner is `TEST_BLOCKED`, not a pass or skip.
- Full acceptance remains
  `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`.

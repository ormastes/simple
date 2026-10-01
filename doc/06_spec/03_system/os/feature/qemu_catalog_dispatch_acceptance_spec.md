# Catalog QEMU dispatch acceptance — host fixture

> **Execution and regeneration pending (2026-10-01).** This is an authored
> mirror of the executable SSpec. It is not a generated or passing SPipe result.
> Run docgen with the admitted self-hosted Simple binary and require zero stubs
> after the runner is available.

## Purpose and scope

The SimpleOS catalog planner and process seam must preserve the same sealed
argv. This manual checks the production dispatch owner against a local
host-process observer. The observer reports each argument it received, writes
a stderr marker, and exits 37. It does not emulate QEMU or boot a guest.

**Evidence class:** `host-fixture`. Requirements: `REQ-001`, `REQ-014`,
`REQ-016`, `UP-AC-005` in
[`simple_platform_unification.md`](../../../../02_requirements/feature/simple_platform_unification.md).
The executable scenario is
[`qemu_catalog_dispatch_acceptance_spec.spl`](../../../../../test/03_system/os/feature/qemu_catalog_dispatch_acceptance_spec.spl).

## Operator workflow

From the repository root, with an admitted self-hosted `bin/simple` and a host C
compiler named `cc`, run:

```text
bin/simple test test/03_system/os/feature/qemu_catalog_dispatch_acceptance_spec.spl
bin/simple spipe-docgen test/03_system/os/feature/qemu_catalog_dispatch_acceptance_spec.spl --output doc/06_spec --no-index
```

The test builds an isolated observer under
`build/test-artifacts/os/qemu-catalog-dispatch-<pid>/`. Run the file alone;
directory-level Simple test runs share a results database and must be serial.
Accept execution only when the runner reports the executed scenario count,
test status, and exit code, after a separate deliberate-red calibration.

## Scenarios

### Every default target yields a sealed command

Resolve the x86_32, x86_64, ARM32, ARM64, RV32, and RV64 catalog default
lanes through the production planner. Every plan must be admitted, validate its
seal, retain its canonical target identity, and expose the exact plan argv to
the dispatch owner, including kernel and SMP options. This checks command
readiness across architectures without
claiming a QEMU process or guest boot on every target.

### The inspected command reaches one real child process

1. Build the host argv observer in an isolated output directory.
2. Resolve the x86_64 catalog default lane into a sealed QEMU launch plan using
   the production planner and a TCG-only host fixture.
3. Inspect both POSIX and Windows command displays: the executable is the
   observer, and the remaining arguments equal the sealed plan's argv in order.
4. Dispatch that plan through `qemu_cli_dispatch_plan_v1`, which uses the
   bounded production process facade.
5. Retain the plan digest, child-observed stdout, stderr, and exit status in
   `build/test-artifacts/os/qemu-catalog-dispatch-<pid>/qemu-argv-observer.exe.dispatch.txt`.
   Require stdout to match every indexed argv atom, stderr to contain the
   observer marker, and process status to equal 37.

This catches argument reordering, omission, shell reparsing, and lost child
status or stderr in the host dispatch path. It does not exercise the `simple os
run` CLI entrypoint or prove that QEMU accepts the argv or boots the image.

### Unsupported acceleration has no dispatch command

Require KVM on a TCG-only host fixture. The production planner must reject the
plan. Dispatch must return an empty stdout, the typed rejection text, and
status -1 before attempting a child process.

### An unbounded deadline is rejected before launch

Bind an admitted catalog plan to a nonexistent executable, then request
deadlines of 0 and 600001 ms. Both calls must return the deadline error and
status -1; a subprocess attempt would instead report a spawn failure.

## Limits and troubleshooting

A missing `cc`, failed fixture compilation, or absent admitted Simple runner is
`MissingEvidence`, never a passing or skipped scenario. The final generated
manual must report all four scenarios and zero stubs. Live-guest acceptance
still requires a real QEMU binary, admitted image, serial transcript, and the
separate production receipt gate in the SimpleOS system test plan.

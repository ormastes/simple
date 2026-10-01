# Sealed QEMU command dispatch

**Manual draft; docgen and scenario execution TEST_BLOCKED.**
Source: `test/01_unit/os/qemu_cli_dispatch_v1_spec.spl`.
Requirements: REQ-001, REQ-014, REQ-016 in Simple platform unification.

## Inspect the command that will be dispatched

1. Resolve the catalog QEMU lane with an executable path containing a space.
2. Inspect the sealed launch command.
3. Dispatch the plan into an executable/argv vector.
4. Check that the executable, argument order and displayed command match.

Expected: no argument is reparsed as shell syntax. The executable scenario
captures the inspected display. No capture has been generated in this run.

## Refuse an unavailable execution domain

Require KVM from a TCG-only host. Check that the plan is rejected, no command
is returned, and dispatch returns the explicit seal/admission refusal before
process execution. This is a negative contract case, not a live host probe.

## Preserve the sealed snapshot

Append a pause option to one returned command copy, then inspect a fresh copy.
The fresh command must equal the original and the seal must remain valid.

## Bound the process deadline

Submit deadlines -1, 0 and 600001 ms. Each returns the documented deadline
refusal before trying the deliberately nonexistent executable.

## Evidence limits and resumption

These scenarios prove command and refusal contracts when executed. A separate
host-process fixture proves dispatch; real QEMU and guest acceptance remain
separate gates. Use the admitted runtime commands in
`doc/03_plan/sys_test/simpleos_sealed_cli_dispatch.md` and replace this draft
with reviewed complete/zero-stub SPipe output. No PASS is claimed here.

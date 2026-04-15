# Agent Task Plan: x86 Dual-Arch QEMU Boot

## Objective

Support both x86_32 and x86_64 cleanly in QEMU, with different CPU/boot contracts per lane and shared browser/desktop logic above the runtime boundary.

## Recommended Architecture

- x86_32:
  - boot/probe lane
  - `qemu-system-i386`
  - `-machine pc`
  - `-cpu qemu32`
  - Multiboot1-friendly validation
- x86_64:
  - full runtime/browser/desktop lane
  - `qemu-system-x86_64`
  - `-machine q35`
  - `-cpu qemu64`
  - long-mode wrapper/runtime validation

## Workstreams

### Agent 1: x86_32 Bring-Up

Owns:

- add x86_32 browser probe
- add x86_32 desktop probe
- add minimal x86_32 browser software entry
- verify direct QEMU boot on `qemu-system-i386`

Success criteria:

- x86_32 probe reaches serial marker and exits through debug port
- x86_32 browser software lane reaches a deterministic pass marker

### Agent 2: x86_64 Wrapper Repair

Owns:

- isolate the oversized `spl_start` prologue/codegen issue
- reduce or eliminate invalid stack reservations
- restore first-marker boot on x86_64 probe images
- keep boot/runtime changes inside the x86_64 wrapper lane

Success criteria:

- x86_64 probe reaches first raw serial marker
- no repeated early `FAULT @ 0x0`

### Agent 3: Runner and Spec Matrix

Owns:

- extend `src/os/qemu_runner.spl` with explicit x86_32 browser/desktop targets
- keep x86_32 and x86_64 QEMU tuples separate
- make `test/system/browser_engine_in_qemu_spec.spl` run the correct lane for each target
- ensure QEMU validation is not satisfied by stale cached spec results alone

Success criteria:

- spec clearly distinguishes x86_32 probe lane from x86_64 full lane
- direct QEMU runs and spec runs agree on first visible markers

## Implementation Phases

### Phase 1

- make x86_32 probe lane pass
- keep scope to raw serial markers and clean exit

### Phase 2

- add x86_32 browser software-render smoke lane
- avoid desktop/browser service dependencies at first

### Phase 3

- repair x86_64 wrapper/codegen boot path
- restore raw probe marker

### Phase 4

- restore x86_64 browser software-render lane
- only then reintroduce desktop/browser integration checks

### Phase 5

- finalize dual-arch QEMU/spec matrix
- lock in explicit per-arch CPU/machine settings

## Risks

- x86_64 wrapper bug may be in codegen/runtime lowering rather than app code.
- x86_32 compiler support may be incomplete in the current app/wrapper build flow.
- Spec caching can create false confidence unless direct QEMU runs remain part of validation.

## Decision Needed

Recommended selection:

- Feature Option A
- NFR Option 2

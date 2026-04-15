# Distinctive Features Completion Closure Plan

**Date:** 2026-04-04  
**Status:** Complete  
**Scope:** Close the remaining distinctive-feature gaps that are **not blocked on physical hardware access**

## Purpose

This plan turns the current README and audit state into a final closure program for the remaining non-hardware gaps in the distinctive-feature story.

The repo is already in much better shape than the old status wording suggested:

- LLVM public-family closure is already done in code and proof, and only needed doc correction
- anti-dummy / anti-stub enforcement is implemented on the main source and compiled CLI surfaces
- active public-facing SFFI/T32/source proof suites now pass `simple verify quality`
- the remaining non-hardware work is now mostly about:
  - finishing the GHDL mailbox-backed simulated remote-interpreter lane
  - reducing the remaining anti-dummy legacy debt enough that the repo can claim “clean enough on active surfaces” without qualification drift

This plan explicitly excludes the hardware-present OpenOCD/TRACE32/ZedBoard completion work. That is handled in the companion hardware plan.

## Current Truth Snapshot

### Already complete enough and should stay that way

- **LLVM full-family public matrix**
  - The matrix in `src/compiler/70.backend/backend/llvm_support_matrix.spl` is already closed to `stable` or `unsupported`.
  - The remaining task was doc alignment, not backend implementation.

- **Math blocks**
  - `m{}` / `loss{}` / `nograd{}` are complete for the promoted torch-backed C/LLVM scope.

- **Anti-dummy / anti-stub on active primary surfaces**
  - Source lint path is active.
  - Compiled CLI path is active through:
    - `simple lint`
    - `simple verify quality`
  - Active public-facing SFFI/T32/source proof packs now pass the gate.

### Still not fully complete and not blocked on physical hardware

1. **GHDL mailbox-backed remote interpreter lane**
2. **Legacy anti-dummy cleanup outside the active public-facing proof packs**

## Completion Goal

After this plan:

- every non-hardware remaining distinctive feature is either:
  - fully implemented and proven, or
  - explicitly removed from the distinctive-feature completion bucket
- the README and unique-feature audit can describe the remaining non-hardware state in one of:
  - `Implemented`
  - `Implemented with bounded scope`
  - `Implemented with qualifiers`
- no non-hardware feature stays “unfinished” only because of stale docs or placeholder tests

## Workstream A: GHDL Mailbox Remote-Interpreter Closure

### Why it is still open

The current GHDL semihost lane is real and promoted, but the mailbox-backed lane is not implemented yet.

Current code truth:

- `ghdl_rv32_semihost` is host-aware and real
- `ghdl_rv32_mailbox` is still `in_progress`
- no mailbox MMIO protocol implementation was found
- no target-side mailbox runtime exists
- no host/testbench mailbox driver exists
- no authoritative mailbox-specific proof spec exists

### Completion target

Promote the mailbox lane to a real simulated remote-interpreter lane that is **distinct from semihosting** and can be used as the debugger-independent simulation-backed proof row.

### Exact deliverables

1. **Mailbox protocol contract**
   - file: `doc/04_architecture/ghdl_rv32_mailbox_protocol.md`
   - must define:
     - MMIO base address
     - command slots
     - response slots
     - status / ready / error semantics
     - sequence id / generation semantics
     - timeout semantics
     - reset semantics

2. **Target-side mailbox runtime**
   - implement a small runtime binding for the simulated RV32 target
   - responsibilities:
     - poll mailbox state
     - decode command
     - execute bounded command set
     - write structured result and completion status

3. **Host/testbench mailbox driver**
   - either in GHDL testbench support or host-side adapter code
   - responsibilities:
     - write commands into mailbox MMIO
     - wait for response
     - decode response deterministically
     - surface failures as lane failures, not silent skips

4. **Mailbox-aware adapter/orchestration path**
   - current `adapter_ghdl_rv32.spl` is semihost/GDB oriented
   - add mailbox-aware execution path, or a second adapter if separation is cleaner
   - lane routing must be config-driven, not spec-local

5. **Authoritative proof specs**
   - mailbox lane smoke
   - mailbox lane result proof
   - mailbox negative cases:
     - no response
     - bad status code
     - protocol mismatch
     - timeout

6. **Lane promotion**
   - update `lane_registry.spl`
   - update `lane_matrix.md`
   - update remote-baremetal completion report

### Supported command subset for milestone

Do not attempt a universal remote interpreter protocol first. Freeze the first milestone to:

- load bounded payload metadata
- execute one bounded remote workload
- report:
  - pass/fail
  - exit code
  - one text or code result field
- reset mailbox state cleanly

### Acceptance criteria

- `ghdl_rv32_mailbox` is no longer `in_progress`
- lane has a real adapter/runtime path
- mailbox proof does **not** depend on semihost output for success
- `simple test` can drive the mailbox lane through the common runner
- result collection is deterministic

## Workstream B: Anti-Dummy Legacy-Debt Closure

### What is already done

The enforcement feature itself is already implemented. The remaining work is backlog reduction in still-active or still-visible parts of the tree.

Primary surfaces already closed:

- `simple lint`
- `simple verify quality`
- active SFFI proof pack
- active T32 proof pack subset
- `src/compiler/90.tools/async_integration.spl`
- `test/system/async_promise_system_spec.spl`

### Remaining debt classes

1. **Active but non-promoted legacy specs**
   - still contain:
     - boolean-wrapper assertions
     - placeholder pass helpers
     - print-based fake skips

2. **Deferred OS / GPU / userlib source areas**
   - still contain real placeholders such as:
     - `pass_todo`
     - `pass_do_nothing`
     - `pass_dn`

3. **Experimental or postponed surfaces**
   - should not block the public feature if properly classified, but the backlog should remain measurable

### Completion target

Move from:

- “implemented with migration debt”

to:

- “implemented and enforced on active repo surfaces, with only deferred/explicitly out-of-scope debt remaining”

### Bounded cleanup set

#### P1: Active public-facing surfaces

Keep these permanently green under `simple verify quality`:

- SFFI proof pack
- T32 proof pack subset
- active compiler/runtime/system specs touched in this pass

#### P2: Next active cleanup targets

Clean these next because they are still active enough to influence trust:

- remaining T32 hardware specs beyond the cleaned subset
- remaining public runtime/system specs with placeholder success paths
- any public CLI/tooling specs that still rely on print-and-return skips

#### P3: Deferred/development-only areas

Do **not** spend closure effort here until the active surfaces are green:

- postponed hardware lanes
- large OS app surface
- GPU experimental backends
- broad archived or `.skip` files

### Enforcement invariants

Keep these invariants after cleanup:

- `simple lint` catches source-level stub bodies and spec placeholder patterns
- `simple verify quality` is the canonical active-surface gate
- sanctioned skip forms use real skip semantics, not print-based placeholder passes

### Acceptance criteria

- all currently promoted public-facing proof packs pass `simple verify quality`
- backlog report is reproducible from one command
- remaining debt is clearly documented as deferred, experimental, or postponed

## Agent Team Breakdown

### Agent A: GHDL mailbox protocol and adapter
- own mailbox contract
- own adapter/runtime plumbing
- own result-channel integration

### Agent B: GHDL mailbox target/runtime + proof specs
- own target-side mailbox runtime
- own mailbox-specific specs
- own negative protocol tests

### Agent C: Anti-dummy active-surface cleanup
- own remaining active specs with placeholder debt
- keep `verify quality` green on promoted packs

### Agent D: Backlog tooling and status reporting
- own one-command backlog measurement
- own docs/report updates

### Main agent
- integrate status
- update README / audit only after proof is green

## Required Verification

### GHDL mailbox

- mailbox lane smoke spec
- mailbox lane bounded workload proof
- mailbox timeout/failure proof
- lane status no longer `in_progress`

### Anti-dummy

- `simple verify quality` on active public-facing proof packs
- `simple lint` on representative source areas
- one current backlog report command

## Completion Rule

This non-hardware closure plan is done when:

1. GHDL mailbox lane is either implemented and promoted, or explicitly removed from the distinctive-feature completion target
2. Active public-facing proof packs are green under `simple verify quality`
3. Remaining anti-dummy debt is only in deferred/experimental/postponed areas
4. README and unique-feature audit no longer carry stale qualifiers for non-hardware reasons

# RV32 Multi-Backend Boot — Agent Tasks

**Feature:** `rv32_multi_backend_boot`
**Date:** 2026-04-02

## Task Split

### Task 1: Research and requirement authoring

- Write the local research, requirements, and plan docs.
- Keep the language precise about what is proven today.

### Task 2: QEMU boot proof review

- Verify the current RV32 SimpleOS boot path stays the authoritative OS boot lane.
- Make sure the docs point at the actual boot artifact and markers.

### Task 3: GHDL remote lane review

- Verify the RV32 composite runner is framed as remote payload execution.
- Avoid claiming OS boot unless the lane gains a real boot contract later.

### Task 4: Hybrid/RTL lane review

- Verify the hybrid simulator and RTL engine are framed as model-level simulation.
- Require real ELF loading and board support before any OS boot claim.

## Coordination Rules

- Do not edit unrelated RV32 or tooling docs.
- Do not change runtime code in this slice.
- If a later implementation adds real boot support to the hybrid lane, that change must come with new acceptance tests and updated terminology.


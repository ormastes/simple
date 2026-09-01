# Isolated Deterministic rt(hal) Provider Comparison

Purpose: verify bounded parent-authoritative comparison contracts for Pure Simple, C, and Rust provider receipts. Audience: HAL and runtime maintainers.

Source: `test/03_system/runtime/hal_provider_comparison_spec.spl`  
Evidence class: executable source contract  
Current execution status: **PENDING/BLOCKED** — no admitted self-hosted compiler is available; this is not live provider-process evidence.

## Preconditions

Each provider needs an isolated, sealed environment; fixed caller-owned regions; exact operation and invocation identity; terminal receipt; and deterministic parent commit authority.

## Operator workflow

1. Build the controlled request and capacity frame.
2. Run the selected alpha, beta, or normal assurance mode.
3. Capture the three child receipts.
4. Compare the bounded normalized oracle.
5. Inject divergence, misplaced provider identity, unreaped worker, or allocation.
6. Verify fail-closed evidence.

## Scenarios

- Unqualified operations default to Critical and alpha-safe comparison.
- Equivalent isolated lanes produce one deterministic parent commit.
- Alpha stops on any difference; beta retains bounded divergence and may commit the preferred lane.
- Normal executes only the preferred provider.
- Misplaced/unreaped receipts and post-seal allocation are rejected.

## Acceptance boundary

Receipt orchestration is executable production logic, but it does not prove OS-level process isolation or representative physical I/O. Those rows remain pending until live Pure/C/Rust workers and environment executors retain child-process evidence.

## Traceability

REQ-009 through REQ-015; NFR-005, NFR-006, NFR-007, and NFR-010.

## Executable source

The complete executable source remains in `test/03_system/runtime/hal_provider_comparison_spec.spl`.

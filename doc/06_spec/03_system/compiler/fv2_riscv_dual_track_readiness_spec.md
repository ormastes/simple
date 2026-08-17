# FV2 RISC-V Dual-Track Readiness

**Status:** `TEST_BLOCKED` — source/manual prepared; no admitted source-matched
pure-Simple Stage-4 CLI is available to execute SSpec, docgen, or
`sspec-maintain`.

**Executable source:**
`test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl`

## Purpose and audience

This manual is for FV2, RTL, and release reviewers validating the boundary
between RVFI interface readiness and actual RISC-V formal proof. It covers
REQ-FV2-015, REQ-FV2-019, NFR-FV2-002, and NFR-FV2-009. A synthetic core can
prove that the checker recognizes or rejects a port manifest; it cannot prove
the generated CPU, Sail oracle, RTL refinement, or SymbiYosys properties.

## Preconditions

- A source-matched, provenance-admitted pure-Simple Stage-4 CLI.
- POSIX `/bin/sh`, `/usr/bin/env`, and `chmod`.
- For the aggregate lane: the generated sidecar inputs and durable Lean/BYL
  proof project required by `check-riscv-formal-dual-track.shs`.
- For strict proof: `sby`, `yosys`, a supported SMT solver, and four generated
  RV32/RV64 proof bundles accepted by the sidecar contract.
- No Rust seed, stale Stage-2/3 binary, hand-authored receipt, or readiness-only
  result may substitute for these prerequisites.

## Operator workflow

1. Confirm the candidate CLI's Stage-4 provenance and source identity.
2. Run the focused SSpec once:

   ```sh
   bin/simple test test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl --mode=interpreter --clean --timeout 900 --sequential
   ```

3. Run maintenance and regeneration once on the unchanged tree:

   ```sh
   bin/simple sspec-maintain scan test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl
   bin/simple spipe-docgen test/03_system/compiler/fv2_riscv_dual_track_readiness_spec.spl --output doc/06_spec --no-index
   ```

4. Require six executed scenarios, zero failures, docgen `0 stubs`, a current
   mirror, and all seven maintenance scores independently accepted.

## Scenario narratives

### Canonical readiness path

- `Prepare a canonical 21-port RVFI core fixture`
- `Run the strict RVFI readiness checker`

The checker must report the complete manifest and readiness marker without an
error. This is checker-readiness evidence only.

### Extended-control edge case

- `Remove the rvfi_mode control port from the canonical fixture`
- `Confirm the checker rejects the incomplete RVFI interface`

The checker must exit 1, name `rvfi_mode`, and omit every readiness marker.
Its internal mutation matrix separately removes `rvfi_halt`, `rvfi_intr`,
`rvfi_mode`, and `rvfi_ixl` one at a time.

### Missing-artifact error path

- `Present a missing generated RVFI core path`
- `Confirm missing Stage-4 artifacts remain blocked`

A missing generated core must exit 1 with `RV32I core VHDL not found`; it must
never become a skip or pass.

### Qualified dual-track proof

- `Run the dual-track aggregate proof gate`
- `Require the generated sidecar and durable manual proof layers`
- `Run the strict RVFI SymbiYosys proof gate`
- `Reject readiness-only or missing-artifact evidence`

The aggregate gate must pass the generated sidecar plus durable Lean/BYL
constraints. The separate strict gate must then report an actual SBY proof
pass. Neither result substitutes for the other.

## Requirement traceability

| Requirement | Scenarios | Evidence boundary |
|---|---|---|
| REQ-FV2-015 | canonical manifest, aggregate gate, strict SBY | RVFI/Sail/SBY dual track; readiness remains distinct from proof |
| REQ-FV2-019 | missing port, missing core, mutation matrix, qualified gates | missing, malformed, readiness-only, and failed evidence reject |
| NFR-FV2-002 | all rejection scenarios | nonzero exits and exact diagnostics remain fail closed |
| NFR-FV2-009 | aggregate gate and strict SBY | independent proof/oracle identities require qualified execution |

## Quality scorecard

| Component | Current result |
|---|---|
| Visible step flow | Source-reviewed: six scenarios with explicit `step("...")` calls |
| Positive/edge/error assertions | Source-reviewed: real exit/status/diagnostic assertions |
| Built-in matchers | Source-reviewed: canonical matchers only |
| Requirement traceability | Source-reviewed: four requirement IDs mapped |
| Runtime execution | `TEST_BLOCKED` |
| Docgen mirror/zero stubs | `TEST_BLOCKED` |
| Seven-part `sspec-maintain` score | `TEST_BLOCKED` |

## Findings and remediation

The source checker previously validated only 17 of the canonical 21 RVFI
ports. It now includes halt, interrupt, privilege mode, and XLEN control ports
and carries an internal deliberate-red matrix. The remaining blocker is not a
test omission: current-main has no admitted Stage-4 CLI or complete generated
proof artifacts. Build and admit that CLI, then run the workflow above once.

## Evidence and provenance

Prepared from `origin/main` baseline `f6cadcc36aff61d16d988651ea36a040d2af6aad`
plus lane commit `c39e708fc220f6cad5df867436557e68eab0b083`.
Static shell self-test passed before this manual was prepared. No runtime,
docgen, maintenance, generated manual, Sail, Lean, or SBY PASS is claimed.

## Compatibility and limitations

The synthetic fixtures exercise textual readiness validation and are not valid
CPU or proof artifacts. The full scenarios require a Linux/POSIX qualified
environment. This manual is an explicitly blocked hand-maintained mirror until
the admitted doc generator replaces it; executable `.spl` remains exclusively
under `test/`.

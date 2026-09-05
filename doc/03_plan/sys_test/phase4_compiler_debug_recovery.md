# Phase 4 compiler debug recovery system-test plan

## Status

`TEST_BLOCKED`: implementation and fail-closed assertions are present, but no
admitted current-source pure-Simple Stage 4 runtime exists. No runtime PASS,
docgen PASS, or `sspec-maintain` score is claimed.

## Scope

The system spec admits the exact Stage 4 candidate, checks compiler/library and
MCP/LSP surfaces, executes the MCP integration, compiles and executes the C5
character ABI probe, runs canonical DAP protocol smoke, and binds the deployed
binary hash to the admitted candidate.

Excluded: Rust-seed evidence, Stage 2/3 substitution, a new bootstrap run,
cross-host/CPU qualification, QEMU, physical targets, release/versioning, and
re-running retained essential-tool smoke outside its admission checker.

## Qualified environment

- Absolute `PHASE4_DEBUG_CANDIDATE` for a current-source pure-Simple Stage 4.
- Absolute adjacent `PHASE4_DEBUG_PROVENANCE` accepted by
  `scripts/check/check-post-bootstrap-stage4-sspec.shs`.
- Absolute `PHASE4_DEBUG_DEPLOYED` local installed executable.
- Lane-owned absolute `PHASE4_DEBUG_ARTIFACT_ROOT`.
- Repository root as current directory, LLVM tools available, and the retained
  Stage 4 smoke/provenance files unchanged.

## Execution order

Run once, after candidate admission:

```bash
PHASE4_DEBUG_CANDIDATE=/absolute/path/to/stage4/simple \
PHASE4_DEBUG_PROVENANCE=/absolute/path/to/stage4/simple.provenance.env \
PHASE4_DEBUG_DEPLOYED=/absolute/path/to/bin/release/<triple>/simple \
PHASE4_DEBUG_ARTIFACT_ROOT=/absolute/path/to/build/test-artifacts/phase4-debug \
SIMPLE_NO_STUB_FALLBACK=1 \
/absolute/path/to/stage4/simple test \
  test/03_system/compiler/phase4_compiler_debug_recovery_spec.spl \
  --mode=interpreter --no-session-daemon --sequential --no-db --no-cache \
  --assert-ran --fail-fast
```

Do not retry a passed row. Stop after the lane-wide three verify/fix-cycle cap.

## Pass/fail criteria

- Every required environment input is nonempty and the candidate version has
  no Rust/bootstrap-seed identity.
- Substituted provenance is rejected; canonical admission reports all exact
  lineage, source-binding, unchanged-smoke, test, lint, and duplicate markers.
- Compiler, library, MCP, LSP, and MCP integration commands exit `0` without
  failed-file or stub-fallback markers.
- The C5 character fixture native-builds and exits exactly `42`.
- DAP smoke emits `STATUS: PASS dap_protocol_smoke`, never SKIP or FAIL.
- Candidate and deployed SHA-256 values are identical.

Any missing input, timeout, signal, skip, unexpected exit, or missing marker is
FAIL. Environment unavailability is `TEST_BLOCKED`, never PASS.

## Manual rendering and capture

The mirrored manual shows all seven operator steps. Helper implementation stays
folded with the executable source; no executable `.spl` belongs under
`doc/06_spec`. Capture text/exec logs and the C5 binary under the configured
artifact root. No GUI or raster evidence applies.

## Traceability

| Requirement | Behavior | Executable scenario | Manual | Status |
|---|---|---|---|---|
| REQ-P4DBG-001 | Inputs and pure-Simple identity fail closed | candidate admission preconditions | `doc/06_spec/03_system/compiler/phase4_compiler_debug_recovery_spec.md` | Future executable |
| REQ-P4DBG-002 | Canonical Stage 4 checker admits exact lineage | post-bootstrap admission | same | Future executable |
| REQ-P4DBG-003 | Compiler and library checks pass | compiler/library checks | same | Future executable |
| REQ-P4DBG-004 | MCP and LSP source checks pass | MCP/LSP checks | same | Future executable |
| REQ-P4DBG-005 | MCP stdio integration executes | MCP integration | same | Future executable |
| REQ-P4DBG-006 | Native C5 character ABI exits `42` | C5 native build/run | same | Future executable |
| REQ-P4DBG-007 | DAP passes and deployment hash binds | DAP/deployment | same | Future executable |

All rows are implemented with real assertions. Runtime coverage remains
`TEST_BLOCKED` until execution by the admitted Stage 4 candidate.

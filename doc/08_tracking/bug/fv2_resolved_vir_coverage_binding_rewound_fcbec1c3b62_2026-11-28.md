# FV2 resolved-VIR semantic-coverage binding rewound by fcbec1c3b62 (2026-11-28)

**Status:** open — product rewind, needs an owner decision on forward-port.
**Found by:** orchestrator native-qualification pre-run, Rust seed interpreter (diagnostic),
`test/01_unit/app/verify/fv2_wave6_orchestrator_spec.spl` 9/12, 3 failing with
`function semantic_coverage_hash_v2 not found`.

## Facts

- The spec (and `test/01_unit/compiler/mir/verification_ir_spec.spl`,
  `test/01_unit/compiler/verification/exact_core_gate_collector_spec.spl`) imports
  `SemanticClass`, `SemanticCoverageV1`, `semantic_coverage_hash_v2` (and the
  `semantic_coverage_for_mir_*_v2` producers) from `compiler.mir.verification_ir`.
- `e274cd33719` (2026-08-27 share-history merge) had `verification_ir.spl`
  `export use compiler.mir.verification_semantic_coverage.{...}` and a
  coverage-bound `ResolvedVerificationIrModuleV2` with
  `semantic_coverage: [SemanticCoverageV1]` + `semantic_coverage_hash: text`,
  `expected_semantic_hash()` folding `|coverage=`, and a `closure_ready()` that
  rechecked the coverage hash and strict variant ordering. It also had stricter
  `VerificationIrFunction.closure_ready` / `VerificationIrModuleV1.closure_ready`
  (schema, symbol id, duplicate called-symbol, member-closure checks).
- `fcbec1c3b62` ("restore src/compiler and src/lib to origin for phase 1
  bootstrap", same day) reverted all of that in `verification_ir.spl`
  (124 lines) and `formal_gate_collectors.spl` (124 lines), replacing the
  re-export with private duplicate `SemanticClass` / `SemanticCoverageV1`.
- `src/compiler/50.mir/verification_semantic_coverage.spl` survived and still
  defines the public coverage API; nothing in `src/` imports it.
- The spec constructs the 6-field struct
  (`ResolvedVerificationIrModuleV2(vir, calls_hash, coverage, coverage_hash, semantic_hash, "")`)
  and assigns `.semantic_coverage_hash`, so re-pointing the import alone only
  moves the failure.

## Why not fixed in the qualification wave

Restoring the binding is a compiler-side change (`50.mir` + `90.tools/verify`,
all struct constructors) on the bootstrap path while a Phase 3 bootstrap lane
is active. Weakening the three specs to the 4-field struct would drop the
coverage-binding assertions. Neither is a spec-only fix.

## TODO

- [ ] Owner decision: forward-port the coverage-bound `ResolvedVerificationIrModuleV2`
      (re-export from `verification_semantic_coverage`, delete the private duplicates,
      restore the stricter `closure_ready` checks) or retire the V2 coverage specs.
- [ ] After a forward-port: run `fv2_wave6_orchestrator_spec`, `verification_ir_spec`,
      `exact_core_gate_collector_spec` before/after on the self-hosted binary.

## Owner decision (2026-11-28)

Deferred: restore the coverage binding in `verification_ir` only after the Phase 3 -> Phase 3 self-build succeeds, so this compiler change cannot disturb the current bootstrap. `fv2_wave6_orchestrator` stays 9/12 (Rust seed interpreter, diagnostic) until then; this record stays open and is the resume point.

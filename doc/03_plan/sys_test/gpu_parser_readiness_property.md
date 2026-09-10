# GPU Parser Readiness Property Gate

Status: **RED / preparation only** (2026-09-10)

This lane qualifies the contracts required before parser work may be admitted
to a GPU implementation. It does not implement GPU kernels, claim GPU
execution, or change the Simple grammar. The CPU reference remains the oracle;
unsupported accelerated seams must fail closed with a reason or an explicit
`MissingEvidence` result.

## Executable source

`test/03_system/app/compiler/feature/gpu_parser_readiness_property_spec.spl`

The single executable spec contains twelve scenarios with stable IDs and
importance metadata. It intentionally fails at each unowned proof boundary so
the release gate cannot be made green by counting CPU fallback as GPU evidence.

## Property matrix

| ID | Property | Evidence required | Current status |
|---|---|---|---|
| GPU-PREP-V001 | generated grammar manifest completeness and digest equality | per-dialect manifest/digest checks: Simple compiler/interpreter/native+Wasm Tree-sitter projection and `.shs`; SdnDialect for SDN; SoshDialect for `src/os/apps/shell/**` | MissingEvidence |
| GPU-PREP-V002 | progress, no epsilon cycle, bounded lookahead, lexical-state composition | finite model checker plus bounded chunk-summary oracle | MissingEvidence |
| GPU-PREP-V003 | stack/action/arena bounds, count/scan/emit determinism, exact-capacity and one-over behavior | checked count/scan/emit receipts and deterministic capacity property suite | MissingEvidence |
| GPU-PREP-V004 | region partition soundness and clean-vs-partitioned parity | ordered disjoint coverage, boundary-state, and fingerprint equality oracle | MissingEvidence |
| GPU-PREP-V005 | deterministic fallback/recovery, cancellation, generation mismatch, malformed UTF-8 | admission/recovery receipt contract with CPU replay and no partial commit | MissingEvidence |
| GPU-PREP-V006 | clean-vs-incremental equivalence | stabilization, reuse, invalidation, and clean-reparse fingerprint equality | MissingEvidence |
| GPU-PREP-V007 | generated-consumer valid-source equivalence | per-dialect generated-consumer corpus run with canonical digest, public API, and diagnostic parity | MissingEvidence |

## Existing passing sub-properties

Before each RED marker, the spec exercises currently owned behavior:

- flat lexical tables validate or reject malformed table shape;
- scalar parsing makes observable progress and reports source bytes read;
- source capacity overflow rejects before token emission;
- sufficient capacity preserves token/output count equality;
- repeated scalar parses preserve the deterministic hash;
- accelerated requests demote to the CPU backend with explicit provenance;
- incremental and partition seams return explicit unsupported errors rather
  than silently claiming equivalence.

The recorded run used:

```text
bin/simple test test/03_system/app/compiler/feature/gpu_parser_readiness_property_spec.spl --mode=interpreter
```

Result: **12 scenarios, 12 explicit MissingEvidence failures**. The failure
is intentional and is the current admission status, not a test harness pass.

## Promotion rule

Remove a `MissingEvidence` marker only when its named production owner exists,
the property is implemented against that owner (not a fixture reimplementation),
and the independent verification lane records the corresponding receipt. A
bounded model/property result is evidence for the tested model/corpus; it is
not a universal proof for all generated grammars. CPU fallback and malformed
recovery remain mandatory and are not counted as GPU success.

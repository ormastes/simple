# Bootstrap compiler/backend stage-split system specification

> Freezes the selected future topology while the current legacy bootstrap
> remains canonical: Rust Stage 1, unchanged canonical pure-Simple Stage 2 and
> Stage 3, then tools-only Stage 4 with zero compiler-source compilation.

| Tests | Active | Skipped | Pending |
|---|---:|---:|---:|
| 10 | 10 | 0 | 0 |

Source: `test/03_system/compiler/bootstrap_compiler_backend_stage_split_spec.spl`

## REQ-BSPLIT-001/002/003 — compiler stages

- Should bind the Rust seed to unchanged canonical Stage 2 and Stage 3 builds.
- Should require typed producer, backend, target, ABI, and content identities.
- Should fail closed rather than substitute a backend or producer.

## REQ-BSPLIT-004/005 — tools-only Stage 4

- Should compile only tool-owned modules and zero compiler-source units.
- Should link the exact versioned Stage 3 interface and archives.
- Should reject compiler traversal and mismatched authority.
- Should execute the built tool only under the admitted Stage 3 identity.

## REQ-BSPLIT-006/007 — migration and audit

- Should keep the legacy pipeline canonical until one admitted success.
- Should keep a full compiler rebuild as a separate audit/equivalence command.
- Should preserve current provenance gates until live split evidence exists.

This is a contract manual, not live artifact evidence. Regenerate it with
SPipe/docgen after the admitted production runner is available.

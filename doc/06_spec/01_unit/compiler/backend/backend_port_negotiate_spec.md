# BackendPortV1 Static Negotiation

- Executable: `test/01_unit/compiler/backend/backend_port_negotiate_spec.spl`
- Requirements: `KPM-NFR-002`, `KPM-REQ-004`, `KPM-REQ-007`, `KPM-REQ-009`, `KPM-REQ-010`
- Evidence class: executable SPipe definition; no execution summary is embedded.

## Scenarios
- negotiates every deterministic table entry.
- uses exact BackendKind names including c and native.
- recomputes the stable domain-framed ABI digest.
- uses only the K1 entries admitted by the committed composition.
- classifies non-bootstrap Wasm as P-static without renaming its cache id.
- rejects a major mismatch with PLUG-E-MAJOR.
- fails closed for an unknown user-visible backend name.

## Selected Policy
- Bootstrap backend: LLVM plus Cranelift (`llvm-cranelift`).

## Freshness
- Requirement IDs and scenario names mirror the executable source as of 2026-09-02.
- The executable contains no `pass_todo` or tautological `expect(true).to_equal(true)` evidence.
- Runtime execution was not available in this audit because the admitted self-hosted `bin/simple` lacks `test`; no runtime PASS is claimed.

# Capability ledger, ownership, and evidence manual

Status: **BLOCKED TRACEABILITY — NOT ACCEPTANCE EVIDENCE**

**Executable source SHA-256:** `877dc47ae6ab0c840e3ff24c1eff3808244a86b5204f2d0ef2fb791700b12286`

**Shared helper SHA-256:** `d122140b3da38a4f9eec9efd9f15936263a916f92b0d701ea7c7ae853afe8c59`

**TUI Captures:** build/test-artifacts/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec/

**Structured ledger evidence:** build/evidence/simpleos/<target>/<environment>/<nonce>/capability_ledger_v1.sdn

## Purpose and audience

Defines fail-closed acceptance for ledger truth, canonical ownership, three environment classes, freshness, duplication, stubs, convergence, and manual quality. This manual is for implementers and reviewers preparing the selected full SimpleOS program.

## Claim boundary

Each executable scenario binds its REQ/NFR and evidence case to a real acceptance owner and an exact expected receipt path. The helper validates a structurally complete `Blocked` candidate through `simpleos_capability_candidate_validate`, then emits `BLOCKED[...]`; no missing receipt can count as PASS. This traceability does not prove implementation, image admission, guest execution, protocol support, performance, QEMU, native-host, or physical-board acceptance.

SPipe regeneration is blocked because the deployed `bin/simple` identifies itself as a Rust bootstrap seed. Regenerate this manual only with an admitted pure-Simple runtime:

`bin/simple spipe-docgen test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl --output doc/06_spec --no-index`

## Operator workflow

1. Prepare an admitted architecture/environment fixture.
2. Run the visible frozen step for the requirement.
3. Invoke the production owner, never a source scan, host fallback, marker, or fixed responder.
4. Capture typed receipt/artifact evidence.
5. Admit the fresh receipt through the production evidence owner before replacing BLOCKED with requirement-specific assertions.
6. Regenerate and review this manual until SPipe reports zero stubs.

## Requirement scorecard

| ID | Behavior | Cases | Current status |
|---|---|---:|---|
| REQ-001 | capability ledger | 3 | BLOCKED: exact receipt not admitted |
| REQ-019 | canonical ownership and duplicate removal | 3 | BLOCKED: exact receipt not admitted |
| REQ-020 | evidence, manuals, and knowledge | 3 | BLOCKED: exact receipt not admitted |
| NFR-001 | architecture evidence | 3 | BLOCKED: exact receipt not admitted |
| NFR-007 | parallel ownership safety | 3 | BLOCKED: exact receipt not admitted |
| NFR-008 | duplication gate | 3 | BLOCKED: exact receipt not admitted |
| NFR-009 | coverage and stub prevention | 3 | BLOCKED: exact receipt not admitted |
| NFR-012 | evidence freshness | 3 | BLOCKED: exact receipt not admitted |
| NFR-013 | convergence guard | 3 | BLOCKED: exact receipt not admitted |
| NFR-014 | documentation quality | 3 | BLOCKED: exact receipt not admitted |

## Evidence and provenance

Required captures are nonce/hash/target-bound `artifact`, `binary`, `exec`, `protocol`, `log`, `gui`, `api`, or `text` evidence under the paths defined by the test plan. QEMU system, native-host, and physical-board receipts remain separate.

## Troubleshooting

A `BLOCKED[<ID>:<case>]` failure names the executable owner, expected receipt file, and exact resume command. Missing runners, images, boards, capture devices, admitted compilers, receipts, or artifacts remain non-PASS. Never change the checker to a tautology or skip.

## Executable mirror

`test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_evidence_manual_spec.spl`

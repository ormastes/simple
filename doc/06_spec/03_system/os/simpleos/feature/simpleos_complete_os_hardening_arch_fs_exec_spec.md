# Architecture, filesystem, and authenticated execution

Status: **BLOCKED TRACEABILITY — NOT ACCEPTANCE EVIDENCE**

**Executable source SHA-256:** `8915b3a9bce96e0079bdd25941711ff109054317b2aca52df04758b248e8340e`

**Shared helper SHA-256:** `d122140b3da38a4f9eec9efd9f15936263a916f92b0d701ea7c7ae853afe8c59`

## Purpose and audience

Defines fail-closed live acceptance for three architectures, FAT32/DBFS/NVFS, authenticated open-handle loading, and durability. This manual is for implementers and reviewers preparing the selected full SimpleOS program.

## Claim boundary

Each executable scenario binds its REQ/NFR and evidence case to a real acceptance owner and an exact expected receipt path. The helper validates a structurally complete `Blocked` candidate through `simpleos_capability_candidate_validate`, then emits `BLOCKED[...]`; no missing receipt can count as PASS. This traceability does not prove implementation, image admission, guest execution, protocol support, performance, QEMU, native-host, or physical-board acceptance.

SPipe regeneration is blocked because the deployed `bin/simple` identifies itself as a Rust bootstrap seed. Regenerate this manual only with an admitted pure-Simple runtime:

`bin/simple spipe-docgen test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl --output doc/06_spec --no-index`

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
| REQ-002 | three-architecture system execution | 3 | BLOCKED: exact receipt not admitted |
| REQ-003 | shared filesystem contract | 3 | BLOCKED: exact receipt not admitted |
| REQ-004 | FAT32 interoperability and recovery | 3 | BLOCKED: exact receipt not admitted |
| REQ-005 | DBFS durability and recovery | 3 | BLOCKED: exact receipt not admitted |
| REQ-006 | NVFS durability and recovery | 3 | BLOCKED: exact receipt not admitted |
| REQ-007 | authenticated executable loading | 3 | BLOCKED: exact receipt not admitted |
| REQ-008 | backend-neutral program execution | 3 | BLOCKED: exact receipt not admitted |
| NFR-006 | authenticated execution safety | 3 | BLOCKED: exact receipt not admitted |
| NFR-011 | recovery and durability | 3 | BLOCKED: exact receipt not admitted |

## Evidence and provenance

Required captures are nonce/hash/target-bound `artifact`, `binary`, `exec`, `protocol`, `log`, `gui`, `api`, or `text` evidence under the paths defined by the test plan. QEMU system, native-host, and physical-board receipts remain separate.

## Troubleshooting

A `BLOCKED[<ID>:<case>]` failure names the executable owner, expected receipt file, and exact resume command. Missing runners, images, boards, capture devices, admitted compilers, receipts, or artifacts remain non-PASS. Never change the checker to a tautology or skip.

## Executable mirror

`test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_arch_fs_exec_spec.spl`

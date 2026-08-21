# Toolchains, userland, and server protocols

Status: **BLOCKED TRACEABILITY — NOT ACCEPTANCE EVIDENCE**

**Executable source SHA-256:** `2269d983d1c6dddf9a52c9739e65dedfc6acdce4be66f77aa0e2d3f43ad35548`

**Shared helper SHA-256:** `d122140b3da38a4f9eec9efd9f15936263a916f92b0d701ea7c7ae853afe8c59`

## Purpose and audience

Defines fail-closed live acceptance for target-native Simple and LLVM/C++, expanded userland, bounded lifecycle, HTTP/DB/RESP/SSH, and security policy. This manual is for implementers and reviewers preparing the selected full SimpleOS program.

## Claim boundary

Each executable scenario binds its REQ/NFR and evidence case to a real acceptance owner and an exact expected receipt path. The helper validates a structurally complete `Blocked` candidate through `simpleos_capability_candidate_validate`, then emits `BLOCKED[...]`; no missing receipt can count as PASS. This traceability does not prove implementation, image admission, guest execution, protocol support, performance, QEMU, native-host, or physical-board acceptance.

SPipe regeneration is blocked because the deployed `bin/simple` identifies itself as a Rust bootstrap seed. Regenerate this manual only with an admitted pure-Simple runtime:

`bin/simple spipe-docgen test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl --output doc/06_spec --no-index`

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
| REQ-009 | target-native Simple roles | 3 | BLOCKED: exact receipt not admitted |
| REQ-010 | full target-native LLVM and Clang profile | 3 | BLOCKED: exact receipt not admitted |
| REQ-011 | expanded Simple userland | 3 | BLOCKED: exact receipt not admitted |
| REQ-012 | unified bounded server lifecycle | 3 | BLOCKED: exact receipt not admitted |
| REQ-013 | full modern web protocols | 3 | BLOCKED: exact receipt not admitted |
| REQ-014 | database protocols | 3 | BLOCKED: exact receipt not admitted |
| REQ-015 | production SSH v2 | 3 | BLOCKED: exact receipt not admitted |
| REQ-016 | server confinement and malformed-input safety | 3 | BLOCKED: exact receipt not admitted |
| NFR-010 | protocol and security policy | 3 | BLOCKED: exact receipt not admitted |

## Evidence and provenance

Required captures are nonce/hash/target-bound `artifact`, `binary`, `exec`, `protocol`, `log`, `gui`, `api`, or `text` evidence under the paths defined by the test plan. QEMU system, native-host, and physical-board receipts remain separate.

## Troubleshooting

A `BLOCKED[<ID>:<case>]` failure names the executable owner, expected receipt file, and exact resume command. Missing runners, images, boards, capture devices, admitted compilers, receipts, or artifacts remain non-PASS. Never change the checker to a tautology or skip.

## Executable mirror

`test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_servers_tools_spec.spl`

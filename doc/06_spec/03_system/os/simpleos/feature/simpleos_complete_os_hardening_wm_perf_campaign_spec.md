# Window manager and production campaigns

Status: **BLOCKED TRACEABILITY — NOT ACCEPTANCE EVIDENCE**

**Executable source SHA-256:** `bf9e2b737f8cb1c7d2c08331db8a175d774b57f1f76396030c88ae353e25a391`

**Shared helper SHA-256:** `d122140b3da38a4f9eec9efd9f15936263a916f92b0d701ea7c7ae853afe8c59`

**Screenshots:** doc/06_spec/image/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec/

**Structured WM evidence:** build/evidence/simpleos/wm/<target>/<environment>/<nonce>/wm_trace.sdn

## Purpose and audience

Defines fail-closed live acceptance for canonical WM interaction/readback, observability, strict performance, fuzz, soak, and lifecycle bounds. This manual is for implementers and reviewers preparing the selected full SimpleOS program.

## Claim boundary

Each campaign row binds its REQ/NFR and evidence case to a real acceptance owner
and an exact expected receipt path. The helper validates a structurally complete
`Blocked` candidate through `simpleos_capability_candidate_validate`, then emits
`BLOCKED[...]`; no missing receipt can count as PASS. Concrete REQ-017 behavior and the
live-guest visual binding now live in
`test/03_system/os/wm/simpleos_wm_behavior_evidence_spec.spl` with the manual at
`doc/06_spec/03_system/os/wm/simpleos_wm_behavior_evidence_spec.md`. That split
does not promote the still-blocked performance, fuzz, soak, lifecycle,
native-host, physical-board, or cross-architecture campaigns.

SPipe regeneration is blocked because the deployed `bin/simple` identifies itself as a Rust bootstrap seed. Regenerate this manual only with an admitted pure-Simple runtime:

`bin/simple spipe-docgen test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl --output doc/06_spec --no-index`

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
| REQ-017 | production SimpleOS window manager | 3 | Supporting behavior/live-QEMU binding moved to the dedicated WM spec; this campaign row remains FAIL until its full matrix closes |
| REQ-018 | observability and performance ownership | 3 | BLOCKED: exact receipt not admitted |
| NFR-002 | strict performance budgets | 3 | BLOCKED: exact receipt not admitted |
| NFR-003 | reproducible measurement | 3 | BLOCKED: exact receipt not admitted |
| NFR-004 | mission-critical robustness | 3 | BLOCKED: exact receipt not admitted |
| NFR-005 | static core and dynamic application bounds | 3 | BLOCKED: exact receipt not admitted |

## Evidence and provenance

Required captures are nonce/hash/target-bound `artifact`, `binary`, `exec`, `protocol`, `log`, `gui`, `api`, or `text` evidence under the paths defined by the test plan. QEMU system, native-host, and physical-board receipts remain separate.

## Troubleshooting

A `BLOCKED[<ID>:<case>]` failure names the executable owner, expected receipt file, and exact resume command. Missing runners, images, boards, capture devices, admitted compilers, receipts, or artifacts remain non-PASS. Never change the checker to a tautology or skip.

## Executable mirror

`test/03_system/os/simpleos/feature/simpleos_complete_os_hardening_wm_perf_campaign_spec.spl`

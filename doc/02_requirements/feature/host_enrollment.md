# Signed host enrollment slice

Status: implementation in progress; target handoff is AWAITING_VERIFICATION. This is the approved finite enrollment slice, not complete host execution.

- HOST-ENROLLMENT-01: Canonical bounded credentials must bind the exact configuration digest, installed public-policy digest, observed machine/boot/provider identity and canonical installed machine parent. Unknown fields, malformed encodings and oversize UTF-8 input reject.
- HOST-ENROLLMENT-02: Existing distinct issuer/approver Ed25519 verification must authorize exactly `host_enroll_v1`, its complete payload, provider environment, host alias, memory ceiling and current policy/session context. Rebinding payload or approval digests without new valid signatures rejects.
- HOST-ENROLLMENT-03: Within an independently trusted installed machine parent, authorize before claiming the slot derived from observed native machine identity. Duplicate or pending slots must not be overwritten, adopted or deleted, including when configuration aliases differ.
- HOST-ENROLLMENT-04: Retain and verify the exact configuration, policy, credential, binding and root manifest before publishing an enrolled claim. Every failure after exclusive claim creation retains the claim and any private root for reconciliation; no operational capacity journal or provider effect occurs in this slice.

Signed values approve supplied bindings; they do not collect native evidence. The future public command must acquire native observations and the installed parent through protected owner mechanisms. Mode bits, configuration flags and arbitrary fresh directories do not establish that provenance. Live execution, restart reconciliation, observations and remote/terminal integration remain outside this bounded slice.

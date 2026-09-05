# PQ Script Signing — TL;DR

Hash-based (SHA-256-only) script signatures: `wots-merkle-sha256-w16-h8`.
Quantum-safe because security is only SHA-256 (2nd-)preimage resistance.

```
sk_seed ──H("wots-sk"…)──> sk[i][0..66] ──F^15──> pk_j ──H("wots-pk")──> leaf[i]
                                                    │  F(x)=H("wots-f"||pub_seed||x)
leaf[0..255] ──H("node"||L||R) pairwise, height 8──> root  == public key (.pub)
sign: m=H("msg"||script); 64 nibbles + 3-nibble checksum; sig_j=F^{b_j}(sk[i][j])
verify: F^{15-b_j}(sig_j) -> leaf -> climb auth path -> must equal root
```

- Keygen (~9 min): `sh scripts/trust/keygen-pq.shs --name N --out config/trust/N.pub`
- Sign: `sh scripts/trust/sign-script.shs --name N FILE…` → `FILE.sig`
- Verify: `sh scripts/trust/verify-script.shs --public config/trust/N.pub FILE…`
  (verdict last line: PASS/FAIL/ERROR; `--selftest` available)
- Simple API: `std.nogc_sync_mut.trust.script_signature.script_signature_verify_file`

HAZARD: keys are STATEFUL, 256 signatures max. Leaf reuse = forgery.
Never copy/snapshot/restore `~/.config/simple/keys/<name>/`. Signer bumps
`next_leaf` before emitting; exhausted keys refuse. Rotate: new keygen, commit
new `.pub`, bump `revocation_epoch` on the old one, re-sign consumers.

Full guide: `pq_script_signing.md`.

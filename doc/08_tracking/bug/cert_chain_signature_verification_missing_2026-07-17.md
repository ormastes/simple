# TLS chain-of-trust signature verification (`verify_signature`) has no implementation anywhere

**Date:** 2026-07-17
**Scope:** `src/lib/nogc_sync_mut/tls/validation.spl` (deleted `validate_chain`)
**Status:** Deliberately deferred, not fixed. Dead code removed rather than
faked; this doc tracks the real gap for whoever picks up TLS chain-of-trust
validation.

## Background

Found while fixing the CERT-IMPORTS lane's standing defect (see
`doc/08_tracking/bug/hir_stmt_expr_payload_extraction_nil_2026-07-17.md`,
final section): `src/lib/nogc_sync_mut/tls/certificate.spl` and
`src/lib/nogc_sync_mut/tls/validation.spl` imported three modules that never
existed in this tree — `std.cert.x509`, `std.cert.chain`,
`std.cert.validation` — blocking phase-1 source collection for any seed
native-build with `--source src/lib`.

`certificate.spl`'s usage (`parse_certificate_der`, `parse_distinguished_name`,
`check_expiry`) was repointed to the real, working typed parser at
`std.cert.x509_typed` (`x509_parse_pem`, `X509Cert`, `x509_cert_cn`,
`x509_cert_issuer_cn`, `X509Cert.not_before_unix`/`not_after_unix`) — that
part of the gap is closed.

`validation.spl`'s `validate_chain(chain, trust_anchors)` additionally called
`verify_signature(cert.parsed, issuer.parsed)` twice (linking each cert to
its issuer, and the root to a trust anchor) from `std.cert.validation`, which
never existed either. Unlike the other three phantom imports, `verify_signature`
has no equivalent anywhere: `x509_typed.spl` exposes parsed signature bytes
(`X509Cert.sig_value`), the TBS signature algorithm OID
(`X509Cert.sig_alg_oid`), and the issuer's public key (`X509Cert.spki_key`,
`X509Cert.spki_alg_oid`) but does not itself verify a signature against a
key — that would require real RSA (PKCS#1 v1.5 or PSS) and ECDSA verify
primitives dispatched by OID, which do not exist in this codebase.
`src/lib/common/jwt/verify.spl`'s `verify_signature(token, jwks_json, alg)`
is JWT-compact-serialization-shaped and not reusable for raw X.509
TBSCertificate-bytes-vs-DER-signature verification.

## Why deleted, not stubbed

`validate_chain` had zero live callers: `grep -rn "validate_chain"` across
`src/` and `test/` found only its own definition plus the three tier
re-export facades (`gc_async_mut`/`gc_sync_mut`/`nogc_async_mut` `tls/validation.spl`)
that re-export it without ever invoking it. The only test coverage of
`std.*.tls.validation` (`test/01_unit/lib/{gc_async_mut,nogc_async_mut}/tls/tls_facade_spec.spl`)
imports `matches_hostname`/`constant_time_compare` only — never `validate_chain`.
Per repo convention ("`NEVER convert TODO/FIXME to NOTE` — implement or
delete entirely"), and given implementing real multi-algorithm X.509
signature verification is out of scope for an import-wall fix, `validate_chain`
was deleted along with its imports rather than left as a broken/no-op stub.
The two named-list re-export facades (`gc_async_mut/tls/validation.spl`,
`nogc_async_mut/tls/validation.spl`) had `validate_chain` removed from their
`export use {...}` lists in the same change; `gc_sync_mut/tls/validation.spl`
is a `.*` star-facade and needed no edit.

## Follow-up (not done here)

To implement real chain-of-trust validation:
1. Add RSA PKCS#1v1.5/PSS and ECDSA (P-256 at minimum) signature verification
   primitives, dispatched by `X509Cert.sig_alg_oid`, taking the issuer's
   `spki_key`/`spki_alg_oid` and the subject's TBSCertificate bytes + `sig_value`.
2. Re-add `validate_chain(chain: TlsCertificateChain, trust_anchors: [TlsCertificate]) -> Result<(), text>`
   to `validation.spl` using those primitives instead of a phantom import.
3. Add real test coverage (currently none existed even for the deleted
   phantom-backed version).

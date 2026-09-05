# TODO: admit SFFI providers with artifact-bound evidence

**Date:** 2026-08-27  
**Status:** BLOCKED — external provider evidence is not available  
**Owner:** SFFI v2 integration owner

## Remaining work

Do not classify any source-contained `rt_*` boundary as verified or signed until
each provider supplies and the loader admits all of the following for the exact
loaded artifact:

- canonical ABI/ownership/nullability contract and provider registry hash;
- artifact SHA-256 plus exact build-input and compiler identities;
- verification receipt(s) bound to those inputs; and
- detached signature plus a configured trusted key/issuer and revocation policy.

Then run the authoritative admission path and refresh the source inventory. A
source-only unsafe scope or static audit is containment evidence only; it does
not establish ABI correctness, provider safety, artifact identity, or signature
admission.

## Completion condition

The loader rejects altered, unsigned, untrusted, ABI-mismatched, null-contract,
and stale-evidence providers before publishing a typed function pointer, and
the inventory reports provider-specific verified/signed admission evidence.

# SimpleOS PBKDF2 imports an exported HMAC adapter with no definition

Phase1 row 23681 executed all three PBKDF2-HMAC-SHA256 known-answer cases and
failed all three before digest comparison: `semantic: function
sha256_hmac_from_list not found`. Original result:
`/tmp/simple-phase1-per-row-attempt-20261006/23681/result.json`; failure output:
`/tmp/simple-phase1-parallel-source-0/build/test-artifacts/unit/os/crypto/pbkdf2/output.log`.
This is frozen diagnostic source e590, seed0f9 evidence, not native admission.

Owner `src/os/crypto/pbkdf2.spl` imports
`os.crypto.sha256.{sha256_hmac_from_list}` and calls it for the PBKDF2 PRF.
`src/os/crypto/sha256.spl` exports that name at line402 but contains no
function definition or import binding for it. The owner does define the
actual typed `sha256_hmac` and `sha256_hmac_with_len` APIs. PBKDF2's existing
comment alleges a historical typed-array runtime issue and prefers the list
adapter; that claim requires actual diagnostic/native evidence before
changing the API path. No invented std helper or stub is an acceptable repair.

Local bug search found native/JIT PBKDF2 provider and signature-key issues,
but no recorded missing exported list-adapter definition. Preserve all RFC
and reference KATs. Repair criterion: implement/bind a real pure-SPL adapter
against existing SHA256/HMAC owner semantics, preserve byte values/lengths
and output, then execute these three previously failed cases once on changed
source with independent provider answers. Native/core/library admission
remains required for any production crypto change; a seed PASS alone is
insufficient. Higher-iteration performance is separately documented and is
not solved by suppressing these failures.

No production source or KAT was edited for this observation. This artifact
is a prepared separate owner task, not part of the manifest fixture fix.

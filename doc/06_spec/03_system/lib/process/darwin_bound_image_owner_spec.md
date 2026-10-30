# Darwin authenticated image owner

Source: `test/03_system/lib/process/darwin_bound_image_owner_spec.spl`.
Native checker: `scripts/check/check-sosix-darwin-bound-image.shs`.
Requirements: REQ-DARWIN-IMAGE-BIND-003 (authenticated provisioning) and
REQ-DARWIN-IMAGE-BIND-004 (actual owner/worker enforcement).

1. Authenticate source memory, provision its new signature, and launch under the
   derived CDHash. Reject malformed command counts/sizes, duplicate signature or
   LINKEDIT commands, invalid signature extents and forbidden loader policies
   even when their source digest matches. Apple's strict signature checker must
   accept valid provisioned output.
2. Compare production private-DER bytes with Apple's serializer, including
   zero and high-bit hash bytes.
3. Reject an incorrect source digest before creating image authority.
4. Replace the image after final userspace validation; require kernel rejection
   before executable constructor/main entry. Mutated pages must terminate the
   process without a successful result; earlier authenticated pages may execute.
   Reject 1 TiB sparse-file growth without an unbounded content rehash.
5. Demonstrate an unconstrained injected library actually executes, then require
   the provisioned owner to deny direct and injected custom dependencies.
6. Run the explicit bound-image worker profile and reject a mismatched manifest
   digest. Keep strict Tree/V4 admission unavailable.

The standalone checker returns 77 off macOS. The SSpec records a pending outcome
there; critical assurance may reject pending, but it must never create a pass or
provider admission. Native fixtures and the production runtime-object regression
suite passed on the development Mac. Deployed pure-Simple/P2 qualification and
cross-OS qualification remain separate.

Recorded 2026-10-29: the final native suite produced thirteen PASS evidence
markers; the modern SSpec executed one example and passed in 3.480 seconds.
SSpec used the authorized P1 diagnostic seed with SHA256
`59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`
and an isolated test root linking `/Users/ormastes/simple/src/lib`. This is
diagnostic wrapper evidence, not pure-Simple/P2 deployment qualification.
The temporary spec was copied directly and compared byte-for-byte with the
repository source; both have SHA256
`2d7c070f600850d4a3197913a569b729bdf9eaaee2d18056c16ded7866a31ab5`.
The production runtime-object checker selects bound-image cases explicitly with
`check-sosix-darwin-snapshot-api.shs --bound-image`; its default cooperative
regression remains independent of private AMFI availability.
UBSan passed the authenticated parser matrix and native signature launch.
ASan coverage is unavailable because the host toolchain runtime deadlocked
before entering the test; it was terminated rather than left running.

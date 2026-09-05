# Simplebox signed installed-catalog record v1

Status: production boundary specified; population remains fail-closed.

The image builder currently stages `/bin/simplebox`, declares eight exact
aliases, and validates an unsigned SHA-256/build-provenance receipt. That
receipt is not cryptographic package evidence and must never populate
`installed_artifact_catalog_v1`.

The producer must emit one immutable `SimpleArtifactManifest` whose entrypoint
is `/bin/simplebox`, whose target matches the selected image architecture, and
whose content hashes include the exact staged payload SHA-256. Its signature
envelope must use the loader's authoritative
`encode_simple_artifact_manifest_v1_signing_bytes(manifest, image_hash)`
projection and the exact `ed25519:<signer-id>:<128-lowercase-hex>` envelope
stored identically in `manifest.signature` and the catalog detached-signature
field. Boot policy selects the matching signer identity and trust-root SHA-256. The exact
alias vector is `/bin/echo`, `/bin/true`, `/bin/false`, `/bin/pwd`, `/bin/seq`,
`/bin/cat`, `/bin/head`, and `/bin/wc`; aliases are metadata and do not create
independent signed artifacts.

Image construction may carry this signed record but must not verify it against
a caller-supplied key or populate the kernel-global catalog. Bootstrap must
load trust roots from authenticated boot policy, verify the manifest with the
loader-owned verifier against the stable staged payload digest, add exactly one
record through the package-private bootstrap session, then seal the catalog.
Any missing field, target/digest/alias mismatch, unknown signer, signature
failure, or unavailable trust policy leaves the catalog unpopulated.

Current blocker:
`simplebox-installer-receipt-has-no-authenticated-manifest-signer-or-signature`.
Resume only after the image-builder input format and on-image metadata carry
the complete signed manifest envelope and authenticated boot policy supplies
the matching trust root. Launcher authority remains out of scope.

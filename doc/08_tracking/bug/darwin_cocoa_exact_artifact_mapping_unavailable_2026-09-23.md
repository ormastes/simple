# Darwin Cocoa exact-artifact mapping is unavailable

Date: 2026-09-23. Status: BLOCKED external packaging prerequisite.

The optional Cocoa provider can be built and exercised diagnostically, but
production activation must remain disabled. `ExactArtifactDynLib.load_exact_linux`
in `src/lib/nogc_sync_mut/sffi/dynamic.spl` rejects Darwin with E-SFFI-020.
`src/runtime/runtime_dynload.c` also fails closed outside Linux for authenticated
GPU snapshots. Neither `spl_dlopen_checked` nor the pre/post pathname hashing in
`dynlib_exact_admission_v1.spl` binds inspected bytes to mapped code before
native constructors execute. The existing Cocoa implementation remains active.

## Candidate preservation, not load authority

The existing bootstrap seed tuple and Phase2 capsule may preserve this pair:

- `libspl_cocoa.dylib`: fixed candidate filename, SHA-256 bound in the capsule.
- `libspl_cocoa.producer.txt`: diagnostic producer receipt, separately SHA-256
  bound, requiring `admission=not-established` and
  `abi=legacy-cocoa-raw-title-v1`.

The capsule aggregate binds both digests plus `cocoa_admission=unavailable` and
`cocoa_dependency_admission=not-established`. Missing pairs, symlink leaves,
wrong ABI/path, duplicate identity fields, altered bytes/receipt, and attempted
admission upgrades fail validation. Older capsules without the optional fields
retain their original aggregate definition but cannot contain undeclared Cocoa
candidate files. Producer dependency observations are provenance only: copying
or hashing an `otool -L` listing does not authenticate dependency code.

No runtime path/handle is exported by this work. No checked typed Cocoa lookup
or exact-byte mapping implementation is claimed. The candidate stays inert;
the seed tuple's existing copy transaction is the sole publication owner.

## Apple platform investigation

Apple's [library validation documentation](https://developer.apple.com/documentation/bundleresources/entitlements/com.apple.security.cs.disable-library-validation)
describes same-Team-ID or Apple-signed admission. That alone does not select an
exact provider revision. Static signature validation followed by pathname
`dlopen` also does not close pathname replacement between the two operations.

macOS 14 added [library constraints](https://developer.apple.com/documentation/security/applying-launch-environment-and-library-constraints)
that the kernel enforces when loading libraries; failed constraints make
`dlopen` return NULL. Apple's [WWDC23 environment constraints talk](https://developer.apple.com/videos/play/wwdc2023/10266/)
explicitly documents a `cdhash` constraint. This is a candidate pre-constructor
integrity mechanism, not a qualified implementation in this repository.
The CodeDirectory identity is distinct from the full artifact SHA-256 required
by the selected manifest; both identities must be bound in admitted provenance.

Read-only inspection on this host (macOS 26.5) found
`bin/release/aarch64-apple-darwin/simple` ad-hoc linker-signed, without Team ID
or internal requirements. Bootstrap/build scripts do not deploy an exact
provider-constrained executable. The separately signed Endpoint Security
collector is not Simple runtime deployment authority. No credentials, signing
identities, or signing configuration were changed.

## Remaining prerequisite and evidence

An admitted packaging owner must supply an OS-enforced pre-constructor mapping
policy, complete dependency closure/identity, and verified process policy.
Embedding an exact provider cdhash in the executable would require re-signing
and re-admitting that executable when the provider changes; this does not yet
meet the unchanged-launcher provider-body-update gate. An alternative protected
generation or existing worker boundary requires separate design/qualification.
Private paths, chmod, pre/post hashes, and a retained raw handle are insufficient.

The capsule contract test exercises candidate copy/verification and negative
mutations only. It does not establish real dependency rejection at mapping,
compiled Simple GUI behavior, no-demand startup/RSS budgets, or production
Darwin exact-artifact admission. No heavy bootstrap was run for this change.
Merge owner: parent macOS integration lane. Sidecars: N/A. Independent review
is required before commit; production activation remains blocked afterward.

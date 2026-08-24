# Installed-artifact filesystem launch manifest-policy blocker — 2026-08-24

Status: policy boundary implemented for the current ELF64 launch subset;
static review pending; no runtime verification performed.

## Intended boundary

The next production owner must connect a sealed, boot-authenticated installed
artifact record and its exact VFS payload to the canonical ELF load plan and
Scheduler adoption transaction for mapping-ready x86-64, AArch64, and RV64.
It must not bootstrap, accept a path-only fallback, or reconstruct loader
authority outside the loader package.

## Blocking authorization gap

A drafted owner correctly added target/path-bound catalog generations, exact
MountTable execute bindings, 16 MiB chunked reads up to 64 MiB, payload hashing,
canonical ELF layout, consume-once authority, scheduler publication, and
generational retry cleanup. Final static review found that it could still mint
authority for any signed catalog record whose bytes happened to parse as ELF.
It did not enforce the signed manifest's `artifact_kind`, `format_version`, or
`required_capabilities` against the selected child capability set. That would
allow a legitimately signed `script`, `smf`, unknown-kind, or under-capability
record to execute contrary to its signed intent. The draft was therefore
removed rather than retained as production code.

## Required safe continuation

Before opening or minting authority, the future owner must:

1. derive the target exclusively from the active platform and perform the
   generation-bound catalog lookup;
2. run the canonical manifest target/format validator and admit only the exact
   executable kind supported by this ELF owner (`elf` initially; any
   `native_simple` policy must be separately explicit);
3. require `(manifest.required_capabilities & child_caps.bits) ==
   manifest.required_capabilities` and route ABI features, required services,
   and resource limits through their canonical admission owners rather than
   ignoring them;
4. preserve the reviewed resource model: <=16 MiB VFS reads, <=64 MiB total,
   post-hash binding/catalog revalidation, typed read/digest/ELF failures, and
   one opaque generational cleanup receipt for either a file handle or loader
   token;
5. independently review exact catalog/alias/target binding, every pre-issue
   close path, Armed/Retrieved/CloseRetryable terminalization, and successful
   scheduler adoption on x86-64, AArch64, and RV64.

The Simple interpreter, compiler, and loader remain required signed catalog
rows. Their filesystem-launch goal is not complete until this policy boundary,
architecture user-entry dispatch, and later QEMU acceptance evidence exist.

## 2026-08-24 continuation

`installed_artifact_manifest_execution_policy_v1.spl` now owns a bounded,
metadata-only catalog-to-load-plan transition. The installed-artifact loader
entrypoint binds the active target, sealed catalog generation, canonical
manifest identity, content digest, exact ELF kind/version, child capability
mask, ABI features, service policy, resource policy, signer identity, and the
boot-verified public-key digest before its first VFS read or authority issue.
The sealed catalog now retains that trust-root digest in its integrity hash so
the per-open trust registry cannot substitute another key under the same key
name. Unsupported services and nonzero resource limits are
intentionally denied until their scheduler/descriptor transaction exists.

This closes the manifest-intent bypass for the supported ELF64 subset. It does
not claim filesystem execution complete: the new path is unverified, requires
independent static review, and still needs a canonical caller plus architecture
entry and QEMU acceptance evidence.

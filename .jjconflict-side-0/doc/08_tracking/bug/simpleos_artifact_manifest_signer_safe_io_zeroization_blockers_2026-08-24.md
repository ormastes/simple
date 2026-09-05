# SimpleOS artifact manifest signer safe-I/O and zeroization blockers

Status: OPEN — unsafe signer draft reverted after independent static review.

The canonical SAM1 signing codec is available, but a robust build-time
`simpleos_artifact_manifest_signer` cannot yet be implemented on the current
host facade without weakening the requested security properties:

1. `src/os/installer/image_bounded_file_reader.spl` records that hosted file
   reads have no O_NOFOLLOW/openat2 handle whose `fstat` identity and bounded
   reads remain tied to the validated object. A path predicate and size check
   followed by a path reopen is TOCTOU-vulnerable for the artifact, descriptor,
   raw seed, and trust configuration.
2. The app-facing I/O owner has no implemented create-exclusive staged byte
   writer plus rename-no-replace operation. A predictable staged path and
   check-before-rename can follow or overwrite a raced path and can replace a
   destination created after the check.
3. `pure_ed25519_sign` retains derived secret arrays (`h`, clamped scalar,
   prefix/nonce material, reduced scalars, and multiplication inputs). Wiping
   only the caller's raw seed does not satisfy whole-operation secret-buffer
   zeroization.

## Ed25519 zeroization audit (2026-08-24)

An independent static review rejected adding a wrapper that wipes only the
arrays visible in `pure_ed25519_sign`. Such a wrapper could produce a verified
`SecureZeroReport` while secret-dependent allocations created by callees were
already unreachable, which would make the receipt materially misleading.

The owner-reachable secret inventory is wider than the public signing frame:

- `ed25519.spl` creates the 64-byte seed hash, clamped scalar, 32-byte nonce
  prefix, prefix-plus-message input, reduced nonce scalar, reduced-secret
  widening buffer, and scalar-dependent point workspaces;
- `ed25519_scalar.spl` allocates `[u32]` reduction, subtraction, selection,
  addition, multiplication, accumulator, and addend arrays repeatedly;
- point multiplication and small-limb field arithmetic allocate nested
  `[u64]` coordinate arrays and scalar-dependent selected/accumulated points;
- `sha512.spl` retains padded input, message schedules, chaining state,
  per-round values, and digest material; and
- any runtime/provider signing branch has opaque internal workspaces and
  currently returns no cleanup attestation.

The current compiler-resistant owner, `secure_memory.spl`, can volatile-wipe
and read back only reachable `[u8]` and `[i64]` allocations. It cannot reach
discarded callee allocations, `[u32]`/`[u64]` workspaces, value-struct copies,
register spills, stack remnants, GC movement copies, optimizer temporaries, or
opaque provider state. Therefore no new API may claim that all derived signing
secrets were erased merely by aggregating wipes in the public signing frame.

The minimum truthful source-level contract is: all explicitly registered,
owner-reachable heap slots were volatile-overwritten and read back as zero;
compiler, GC, ABI, register/stack, and provider copies remain explicitly out of
scope. Closing even that narrower contract requires a coordinated redesign:

1. Add typed compiler-resistant `[u32]` and `[u64]` wipe owners.
2. Replace allocating SHA-512 signing use with a single mutable owned context
   whose consuming finish path wipes padded data, schedule, state, and digest.
3. Replace allocating scalar reduction/multiply-add with one fixed mutable
   workspace and in-place operations followed by consuming cleanup.
4. Replace allocating point multiplication with a fixed owned limb workspace
   and table, or use an audited provider that returns a cleanup receipt.
5. Route every success, error, fallback, and dual-provider path through one
   cleanup exit that reports exact registered and cleared slot counts.
6. Make the seed ownership explicit: either consume a unique secret owner or
   exclude the caller-owned seed from the cleanup claim.

A stronger physical-erasure claim additionally requires a non-moving unique
secret-memory ABI, compiler/runtime no-copy guarantees, stack/register
scrubbing, and heap-forensics evidence. None exists in the current tree.

Required prerequisites are therefore:

- a pure-Simple typed hosted file owner that opens no-follow, snapshots identity
  and size with `fstat`, performs bounded reads on that same handle, and closes
  exactly once;
- a create-exclusive, no-follow staging handle and atomic rename-no-replace
  publication primitive; and
- a zeroizing pure-Simple Ed25519 public-key derivation/signing entrypoint that
  reports wipe failure and clears every explicitly registered owner-reachable
  secret workspace under the audited contract above.

## Safe-I/O provider update (2026-08-24, unverified)

The first two safe-I/O prerequisites now have a Linux provider draft in
`src/os/installer/hosted_safe_artifact_io_v1.spl`.  It retains a package-bound
trusted-root descriptor, uses kernel-enforced `openat2` beneath/no-symlink/
no-magic-link/no-mount-crossing resolution for reads and destination parents,
uses unnamed private `O_TMPFILE` staging, publishes the exact fd with atomic
absent-destination `linkat(AT_EMPTY_PATH)`, and orders data/file/directory
durability.  Interpreter and native C entrypoints share the failure classes.
The Pure Simple owner consumes positive-generation sealed grants so copying a
grant cannot redeem it twice.  This draft has received only static review; no
test, build, SPipe, benchmark, optimizer, or runtime verification was run.

The signing secret-workspace zeroization prerequisite remains open, so the
signer remains blocked even after this I/O boundary is accepted.

Static facade audit (2026-08-24):

- `std.io.FileHandle` retains an fd for read/metadata/flush/close, but
  `rt_io_file_open` exposes only read/write/read-write/append modes and follows
  the supplied path.  Preceding it with `file_is_regular_no_follow` remains a
  check/open race.
- `rt_file_create_excl` supplies create-exclusive as a one-shot path operation,
  but does not return an owned staging handle and its native provider opens
  without `O_NOFOLLOW`/`O_CLOEXEC`; its native implementation performs one
  write rather than an interruption/short-write completion loop.  It cannot
  support fd-bound identity, fsync, or precise cleanup ownership, and the
  path-based `rt_file_sync` would reopen the name after creation.
- `file_rename` has replacement semantics and no rename-no-replace result.  A
  destination existence check cannot repair this because the destination can
  be created between check and rename.
- The compiler memory-snapshot descriptor owner uses the required no-follow
  directory walk and exclusive leaf open internally, but its API accepts only
  fixed snapshot records.  It provides neither arbitrary bounded reads nor
  general staged publication and must not be repurposed as a signer channel.

The exact owner lifecycle and failure semantics are recorded in
`doc/05_design/os/installer/hosted_safe_artifact_io_v1.md`.  Implementing them
requires new canonical host-provider primitives (with interpreter/native
parity); a pure-Simple wrapper over the current facade cannot make the missing
atomic guarantees true.

After those land, the signer can strictly parse exactly one key id/public
key/public-key-hash trust record, require the manifest's content-hash vector to
equal the singleton artifact hash, sign canonical SAM1 bytes, self-verify, and
emit a versioned full record whose decoder rejects trailing data.

No tests, builds, lints, optimizer, SPipe, benchmarks, or runtime verification
were run. This record is based on read-only source inspection.

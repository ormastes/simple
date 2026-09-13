# Hosted safe-artifact native provider V1

Date: 2026-09-13. Scope: the four provider calls consumed by
`os.installer.verified_image_composition_owner_v1` through the shared
`os.installer.hosted_safe_artifact_io_v1` owner.

## Implementation

`src/runtime/runtime_hosted_safe_artifact_v1.c` is instantiated once by
`runtime_native.c`; its public signatures are in the adjacent header. The
self-hosted compiler's `50.mir/text_extern_abi.spl` expands the root-open text
argument at index 0 and read/publish pathname argument at index 1. Root handles
and array payloads remain single ABI values.

The Linux provider keeps up to 32 root descriptors in a mutex-protected registry.
Positive tokens are never reused, including after close; token exhaustion fails
closed. Root acquisition walks every absolute component with `O_NOFOLLOW` and
records directory device/inode identity. Operations resolve beneath that retained
root using `openat2` with `RESOLVE_BENEATH`, `RESOLVE_NO_XDEV`,
`RESOLVE_NO_SYMLINKS`, and `RESOLVE_NO_MAGICLINKS`.

Read admits regular files only, caps allocation and transfer at the requested
bound (maximum 16 MiB), compares descriptor identity/size/mode and nanosecond
mtime/ctime before and after transfer, closes the descriptor, then returns an
owned packed byte array. Failure is canonical native nil (`rt_value_nil()`, raw
3); raw zero is a present value and cannot represent failure. A valid empty file
is an empty array.
`O_NONBLOCK` prevents a FIFO substitution from blocking before the type check.

Publish copies a validated runtime byte array and creates an unnamed `O_TMPFILE`
inode in the retained destination directory. After complete transfer, file sync,
and identity/size validation, `linkat(AT_EMPTY_PATH)` publishes it only if the
destination is absent. It never overwrites a regular file or symlink. Directory
sync and close finish the durability fence. Status -4 means publication happened
but its durability or close fence failed; -5 means prepublication cleanup failed.
Close is never retried after EINTR because Linux may have reused that descriptor.

Non-Linux and freestanding profiles return explicit unsupported/failure results.
No pathname-based fallback weakens the Linux guarantees when openat2 or O_TMPFILE
is unavailable.

## Focused evidence

- PASS: standalone provider compile with C11, `-Wall -Wextra -Werror -pedantic`.
- PASS: `rt_hosted_safe_artifact_v1_selfcheck.c` linked with the actual
  `runtime_native.c`, using `SIMPLE_HOSTED_SAFE_ARTIFACT_TEST_V1`, section garbage
  collection, pthread, dl, and m. This executes real Linux filesystem operations.
- PASS: forced unsupported implementation and its dedicated selfcheck.
- BLOCKED: `bin/release/simple test
  test/01_unit/compiler/mir/hosted_safe_artifact_text_abi_spec.spl
  --mode=interpreter` refused the deployed aarch64 executable as non-production.
  No Rust-seed fallback was used as acceptance evidence.

The native selfcheck covers binary bytes and empty arrays, root and intermediate
symlinks, traversal/embedded NUL paths, FIFOs/directories, strict read bounds,
missing files, interrupted/error reads, metadata mutation, close errors,
exclusive publication, rejected payloads, unsupported syscalls, write/sync/link
failure, prepublication cleanup failure, postpublication durability failure,
concurrent publishers, registry capacity, root pathname replacement, stale
handles, and close failure consumption. Failure injection is compiled only into
the test build. Final directory removal proves no named staging artifacts remain.

### Review correction, 2026-09-14

Astra found a P1 ABI error in the first implementation: failure returned raw zero
and the first selfcheck incorrectly expected zero. Native `rt_is_none(0)` is
false, so a caller could admit the failed read as a present empty value. Every
read failure, allocation/conversion failure, and unsupported-platform read now
returns `rt_value_nil()` (raw 3). The direct ABI probe and all negative read
assertions now check both exact nil encoding and the actual `rt_is_none` /
`rt_is_some` predicates. Valid empty and nonempty reads assert present values.
Allocation/conversion failure injection covers the previously implicit exits.

Corrected evidence: PASS for the full native selfcheck and forced-unsupported
selfcheck, each linked against `runtime_native.c` so the optional predicates are
the production implementations; PASS for strict standalone provider compilation.

The earlier native PASS did not establish optional-value ABI correctness and is
superseded by the corrected selfchecks. Native Simple execution remains
**MissingEvidence**; this correction does not replace the pending admitted
self-hosted compiler/facade execution gate.

## Limits and remaining work

This is native boundary evidence, not compiler-in-SimpleOS or release evidence.
The C selfcheck does not establish that an admitted self-hosted compiler emits
and executes these calls correctly; the focused Simple spec and wider compiler
checks remain required when an admitted runtime is available.

Descriptor snapshots detect observed mutation; they do not provide an immutable
snapshot against a hostile concurrent writer, hard-link isolation, or ownership
against arbitrary native code that closes another component's descriptors.
Retained directory authority follows its inode if another actor renames that
directory; it does not continuously revalidate the logical root pathname.

The separate native `rt_hosted_safe_artifact_bundle_begin_v1` still accepts a
root pathname, while the current Simple facade passes a retained handle. That
existing ABI drift is **not fixed or qualified by this change**. Bundle variants
must not be admitted through these four-call image-provider checks. Native
macOS, Windows, FreeBSD, and SimpleOS provider implementations remain separate
qualification work.

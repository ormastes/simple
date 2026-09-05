# sha3.spl untyped-list boxing corrupts SHA-3 digests (same family as sha256_core, harder shape)

**Status:** RESOLVED 2026-08-12 — retyping to `[i64]` (the sha256_core recipe) WAS
sufficient; the earlier "failed fix" was a stale-stdlib-root measurement trap,
not an algorithmic failure.
**Found:** 2026-08-12, during a sweep for other instances of the
`sha256_core_value_tagging_corrupts_live_digests_2026-08-11` defect family.
**Severity:** HIGH — `sha3_256_bytes`/`sha3_384_bytes`/`sha3_512_bytes` are
live public API and produced wrong digests.

## Root cause (two stacked causes)

1. **The actual corruption — READ-side untyped-list boxing, same as
   sha256_core.** `.get()` on an untyped `list` returns a tagged/boxed i64
   (`value << 3 | tag`); `print` decodes it, but arithmetic and function-arg
   passing operate on the raw tag bits. Differential probe results
   (2026-08-12, seed `bin/simple run`):
   - `rotl64(u.get(0), 1)` on an untyped-list value returned `160` for
     stored `20` — i.e. `rot(20<<3, 1)`; inside keccak the ρ-offsets arrived
     as `r*8 & 63`, scrambling every rotation.
   - Bracket index-assignment (`s[i] = expr`) is **innocent**: probes on both
     typed and untyped lists showed writes and read-back bit-exact. The bug
     doc's write-side suspicion is disproven.
   - Even `i64`-typed callee params (`rotl64(value: i64, ...)`) do NOT unbox
     a tagged argument; the tag must be prevented at the producing list.

2. **Why the first retype attempt looked like a failure:** the deployed seed
   `bin/simple` loads the stdlib from a SECOND root,
   `/mnt/data/build-clean/src/lib/**` (visible via strace: the run opens
   `/mnt/data/build-clean/src/lib/common/crypto/sha3.spl`, and its
   deprecation warnings cite that root). Edits to the repo's
   `src/lib/common/crypto/sha3.spl` were therefore never executed; the
   digest output "changed but stayed wrong" only because the corrupt bytes
   are nondeterministic heap-pointer bytes. Retyping the file in the root
   the binary actually loads produces FIPS-exact digests immediately.
   This is the `reference_bin_simple_symlink_stale_scratch_build` /
   stale-inputs trap family — **verify which stdlib root a binary loads
   (strace open of the edited file) before judging a stdlib fix failed.**

## Fix

`src/lib/common/crypto/sha3.spl`: retyped every `list` annotation to
`[i64]` (all fn return types and params, the context tuple
`([i64], [i64], i64, i64)`, internal `var s/c/d/b/out/tmp` locals, and the
tuple-destructured `var state: [i64] = ctx[0]` / `var buffer: [i64] = ctx[1]`
in `sha3_update`/`sha3_finalize`; stream `chunks` typed `[[i64]]`).
No algorithm or mutation-style changes were needed — in-place
`s[li] = expr` is fine once element reads are untagged.

## Verification (FIPS 202 / NIST example vectors, seed interpreter, std path)

All exact matches (cross-checked against python hashlib):

- SHA3-256(""), SHA3-256("abc"), SHA3-384(""), SHA3-384("abc"),
  SHA3-512(""), SHA3-512("abc"), and streaming `sha3_256_stream([[97],[98,99]])`
  == one-shot "abc".

Specs: `test/01_unit/lib/common/crypto/sha3_kat_spec.spl` (mirrored at
`test/unit/...`) now 7/7 PASS; `hmac_sha3_spec.spl` 6/6 PASS.

## Residual / flagged

- `src/lib/common/crypto/sha1.spl` still carries ~20 untyped `list`
  annotations — same vulnerability class, not audited this session.
- The compiler defect itself (untyped-list `.get()` yielding tagged values
  that survive into arithmetic; typed params not unboxing) remains open at
  the compiler level; `[i64]` retyping is the stdlib-side mitigation, same
  as sha256_core.
- Deployment note: the fix must exist in whatever stdlib root the running
  binary loads (here also synced to `/mnt/data/build-clean/src/lib/...`).

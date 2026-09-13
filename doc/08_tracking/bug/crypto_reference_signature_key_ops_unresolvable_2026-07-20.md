# `std.signature.key_ops` has only a compiled `.smf` artifact, no `.spl` source — module unresolvable under test

- **Date:** 2026-07-20
- **Area:** `src/lib/common/signature/key_ops.smf` (and siblings)
- **Severity:** medium (whole spec file cannot load; 0 examples run).
- Status: PARTIALLY-RESOLVED (2026-09-12) — the unresolvable import is gone and the 7 examples now execute; 4 of them fail on a separate missing-API gap, see Triage 2026-09-12 (second)

## Symptom

```
SIMPLE_RUST_SEED_WARNING=0 timeout 90 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/unit/lib/crypto/crypto_reference_spec.spl --no-session-daemon
```

```
error: semantic: Cannot resolve module: std.signature.key_ops
error: test-runner: no examples executed
```

## Root-cause hypothesis

`test/unit/lib/crypto/crypto_reference_spec.spl:8` imports
`use std.signature.key_ops`. `ls src/lib/common/signature/` shows:

```
create.smf  key_ops.smf  mod.smf  sign.smf  types.smf  utilities.smf  verify.smf
```

Every file in that directory is a compiled `.smf` (Simple Module Format)
artifact — there is no `.spl` source file for `key_ops` (or any sibling) in
the tree. The module resolver used by `simple test` apparently only
resolves modules from `.spl` source, not from a bare `.smf` binary, hence
"Cannot resolve module". This looks like a build/packaging gap: either the
`.spl` source for `std.signature.*` was deleted/never-committed while only
its compiled output survives, or `.smf`-only modules require a different
loading mechanism that isn't wired into the `simple test` path.

This is unrelated to the four other imports in the same spec file
(`std.crypto.constant_time`, `std.crypto.legacy_hash`, `std.crypto.sha1`,
`std.crypto.pbkdf2`, `std.crypto.types`), which all resolve fine — only the
`std.signature.key_ops` import fails, and it fails at whole-file semantic
resolution, so all examples in the file are blocked.

## What NOT to do

This cannot be fixed from `test/**` — the missing artifact is a source-tree
gap, not a spec authoring issue.

## Affected specs

- `test/unit/lib/crypto/crypto_reference_spec.spl` (0 examples executed —
  load failure)

## Triage 2026-09-12
Rule B: re-ran `bin/simple test test/unit/lib/crypto/crypto_reference_spec.spl` on the deployed seed; it still FAILs, matching the recorded defect. Status word left as-is. Binary: /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.

## Triage 2026-09-12 (second pass — fixed)

Binary: `bin/simple` = shared clone's Rust seed, `sha256 3d120a6f…`, aarch64.

The "What NOT to do" section above says this cannot be fixed from `test/**`
because the missing artifact is a source-tree gap. That reasoning assumed the
spec *needs* `std.signature.key_ops`. It does not: the import is bare
(`use std.signature.key_ops`, no symbol list) and **no symbol from it is
referenced anywhere in the file** — the only two matches for
`sign|verify|keypair|public_key` in the whole spec are the header comment and
the import line itself. The four describe blocks are `constant_time_compare`,
legacy-hash KATs, and PBKDF2 vectors.

`src/lib/common/signature/` no longer exists at all — not even the `.smf`
artifacts this record listed — so the import is dead, and deleting it is the
correct fix rather than a workaround.

```
before:  declared>=7 executed=0 passed=0 failed=0   (Cannot resolve module: std.signature.key_ops)
after:   declared>=7 executed=7 passed=3 failed=4
```
(identical in both `test/01_unit/lib/crypto/` and `test/unit/lib/crypto/`; the
pair was already diverged before this change and still is, so the divergence
delta is unchanged.)

**What the load failure was hiding, now OPEN as its own gap:** three functions
the spec imports do not exist —

- `md5_hex` (`std.crypto.legacy_hash`): no `fn md5_hex` anywhere in `src/lib/`.
- `pbkdf2_sha256` / `pbkdf2_sha512` (`std.crypto.pbkdf2`): only the
  `*_bytes` forms exist (`src/lib/common/crypto/pbkdf2.spl:179,229`), taking
  `[i64]` password/salt rather than the text+hex form this spec calls.

Adding text/hex wrappers is an API decision with this spec as the only known
consumer, so it was not guessed at here. The `constant_time_compare` and SHA-1
KAT examples pass.

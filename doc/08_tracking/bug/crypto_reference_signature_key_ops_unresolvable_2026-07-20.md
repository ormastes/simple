# `std.signature.key_ops` has only a compiled `.smf` artifact, no `.spl` source — module unresolvable under test

- **Date:** 2026-07-20
- **Area:** `src/lib/common/signature/key_ops.smf` (and siblings)
- **Severity:** medium (whole spec file cannot load; 0 examples run).
- **Status:** OPEN.

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

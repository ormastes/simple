# Stale cargo cache resurrected a pre-fix seed binary on CI (beta.11 windows leg)

Date: 2026-09-18
Lane: release v1.0.0-beta line (kimi-20260915-beta2)
Severity: release-blocking (wasted an entire 3h release cycle)
Status: fixed in v1.0.0-beta.12

## Symptom

v1.0.0-beta.11's windows-x86_64 leg died with the byte-identical error to
beta.10:

```
error: semantic: unknown extern function: rt_file_read_regular_no_follow_last_failure
```

— even though beta.11 merged the exact fix (PR #1083) and a local probe with a
fix-built seed resolved the call (verified plain and under
SIMPLE_STRICT_EXTERN=1: `arm=4`).

## Cause

Both release.yml and build-binaries.yml cache `src/compiler_rust/target` with
`actions/cache@v4`:

```
key: <os>-rust-bootstrap-<hashFiles(Cargo.lock)>
restore-keys: <os>-rust-bootstrap-        # prefix fallback
```

The prefix restore-key resurrects ANY previous cache for the OS. The restored
`target/` carries cargo fingerprints that do not capture workspace-crate
source changes across tags, so cargo reports the workspace crates "fresh" and
links a seed built from older sources. Beta.11's windows seed therefore
predated the interpreter-extern fix; it hit the bug the fix addressed.

Local proof of the mechanism: the same one-file repro
(`extern fn rt_file_read_regular_no_follow_last_failure(); ... call it`)
fails with the identical E-SFFI-001 error on a pre-fix seed and prints `arm=4`
on a fix-built seed.

## Fix

"Invalidate stale workspace-crate fingerprints" step after every such cache
restore: `find src/compiler_rust -maxdepth 3 ( -name lib.rs -o -name main.rs )
-not -path "*/vendor/*" -exec touch {} +`. Touching the workspace roots sets
their mtimes newer than any restored fingerprint, forcing cargo to rebuild
exactly the workspace crates (~5 min) while keeping the expensive dependency
cache. Applied in release.yml (macOS/Windows cache) and build-binaries.yml
(both restore sites).

## Follow-up ideas (not done)

- Key the cache on a hash of the non-vendor compiler sources instead of
  Cargo.lock (hashFiles over vendor is too broad; needs a generated manifest).
- Generate a `seed-build-id` file embedding the git sha at configure time and
  refuse to run if the binary's id mismatches the checkout.

# Windows bootstrap silently exceeds MAX_PATH; `cl.exe` fails with exit 1 and no diagnostic

- **Date:** 2026-08-30
- **Status:** RESOLVED (2026-09-10 structural fix; regression strengthened
  2026-09-22; re-verified green 2026-11-11, lane boot16 — see addendum)
- **Host:** Windows 11, MSVC 14.44.35207, clang-cl/cl via cc-rs

## Symptom

The Rust seed build fails:

```
error occurred in cc-rs: command did not execute successfully (status code exit code: 1):
  "...\cl.exe" ... "-Fo<path>\37be46648adf0aaa-runtime_backend_plugin.o"
    "-c" "...\runtime_backend_plugin.c"
```

**`cl.exe` prints nothing.** No `error C…`, no `fatal error`, just exit 1. That
is what makes this expensive: it reads as a compile error in a specific file, so
the natural response is to inspect that file's source — which is fine.

## Root cause

The `-Fo` path is **261 characters. Windows `MAX_PATH` is 260.**

```
failing (runtime_backend_plugin.o): 261   -> exit 1, no message
succeeding (ring curve25519.o):     239   -> exit 0
```

Measured directly from the two commands in the same build log. Nothing is wrong
with the file: compiled by hand it succeeds under every configuration tried —
with and without `-I`, and under a minimal `env -i` carrying only
INCLUDE/SystemRoot/SystemDrive. Only the output path length differs.

The length comes from the bootstrap's own directory structure:

```
<repo>/build/bootstrap/<lane>/rust-authority-<64 hex>/target/
  x86_64-pc-windows-msvc/bootstrap/build/simple-runtime-<16 hex>/out/
  <16 hex>-<source stem>.o
```

`rust-authority-` plus a 64-character digest is 79 characters before the cargo
target tree adds ~120 more. Whether a build succeeds then depends on the length
of the **repo checkout path** and of the longest **source file stem**.

## Why this had not been seen

The same tree at `C:\Users\ormas\dev\simple` produces 254 — six characters under
the limit. This run used a worktree at `C:\Users\ormas\dev\simple-rebase`, seven
characters longer, which crosses it. So the lane is not "working" on the shorter
path; it is **one rename, one nested directory, or one longer source filename
away from breaking**, with a failure mode that names an innocent file and prints
nothing.

## Workaround applied

`--output=build/w` instead of `--output=build/bootstrap/win-msvc`, which removes
17 characters. This is a workaround, not a fix.

## Real remedies (not chosen here — each is a policy decision)

1. **Long-path support.** `\?\` prefixes, or the machine-wide
   `LongPathsEnabled` registry setting plus a manifest. Affects the whole
   toolchain and is host configuration, not a repo change.
2. **Shorten `rust-authority-<64 hex>`.** A 16-character prefix of the digest
   would save 48 characters and keep collision resistance far beyond what a
   per-machine build directory needs. This is the highest-value single change,
   but it touches lane identity, which the bootstrap treats as load-bearing.
3. **Shallower cargo target dir** for the authority build.

## Detection

The Windows selector now keeps the Cargo target at
`<repo>/build/c/<full-input-fingerprint>`, outside the deep authority receipt,
HOME, and log tree. It preserves the complete 64-hex input identity and uses
the existing authority lock; Unix still uses `<authority-root>/target`.

Before Cargo starts, the selector converts the target to its native Windows
spelling and rejects a prefix longer than 120 bytes. That reserves 120 bytes
for Cargo, cc-rs, crate, and object nesting under a conservative 240-byte
budget. A checkout that cannot meet the budget now fails with an actionable
message instead of allowing MSVC to exit silently at its path limit.

`test/01_unit/scripts/bootstrap_windows_cargo_path_budget_test.shs` verifies
the original deep legacy layout crosses the limit for both the original
`runtime_backend_plugin.o` shape and the `libmimalloc-sys` shape, while the
new target paths stay within the budget. It also verifies unchanged-fingerprint
reuse, changed-fingerprint isolation, the 120-byte boundary, fail-fast behavior
one byte over, and preservation of the Unix target location.

Focused Windows evidence on 2026-09-22: the regression reported legacy
`runtime_backend_plugin.o` at 279 bytes and the Windows-safe target at 236;
the current checkout measured 215. The lock-host policy regression also passed,
showing that early shared authority ownership remains Windows-only.


---

## Triage addendum 2026-11-11 (lane boot16)

**Verdict: FIXED (re-verified).**

Re-ran the regression test on this checkout (origin/release/1.0.0 tip + ne13/boot11
commits), Windows-native Git Bash host:

    sh test/01_unit/scripts/bootstrap_windows_cargo_path_budget_test.shs
    -> PASS: Windows Cargo path budget; mimalloc_old=264 mimalloc_new=169
       runtime_backend_plugin_old=279 runtime_backend_plugin_new=184 prefix=67
       reserved_max=187 configured_mimalloc=166 configured_runtime_backend_plugin=181

The legacy deep layout still reproduces the over-MAX_PATH object path (264 and
279 bytes, past the 260 limit); the shallow configuration-keyed target
(`build/c/<12-hex config key>`, `bootstrap-authority-wiring.shs`
`bootstrap_authority_rust_cargo_target`) keeps every object path under the
240-byte conservative budget. Structural fix confirmed present and effective.

**One stale assertion corrected** (test-only, no behavior change): the test's
call-site contract check required the literal `cxx=${CXX` inside
`bootstrap-from-scratch.sh`'s `rust_authority_toolchain_extra=` line. The call
site now routes CXX through `rust_authority_cxx` (`rust_authority_cxx=${CXX:-}`,
deliberately cleared on Windows where cc-rs/clang-cl ignores CXX — comment at
`bootstrap-from-scratch.sh:3594`). Updated the required field to
`cxx=${rust_authority_cxx` and added a derivation guard (`rust_authority_cxx=${CXX:-}`)
so the test's intent — CXX must feed the cache-isolation config key — is
preserved, not weakened. Before this correction the test failed at that
assertion and never reached the path-budget fixtures.

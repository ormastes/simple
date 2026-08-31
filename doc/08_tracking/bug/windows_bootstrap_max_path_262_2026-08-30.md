# Windows bootstrap silently exceeds MAX_PATH; `cl.exe` fails with exit 1 and no diagnostic

- **Date:** 2026-08-30
- **Status:** OPEN (worked around by shortening the output dir; the structural
  cause is unfixed)
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

There is no guard for this. A check that asserts the longest `-Fo` path a lane
will generate stays under 260 on Windows would have caught it before the build
started, and would keep catching it as filenames grow. Worth adding.

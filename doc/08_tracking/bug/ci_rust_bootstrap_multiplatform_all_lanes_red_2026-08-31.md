# Rust Bootstrap Multiplatform: every lane red, four independent causes

**Date:** 2026-08-31
**Status:** OPEN (2 of 5 causes fixed elsewhere; 3 remain)
**Workflow:** `.github/workflows/rust-bootstrap-multiplatform.yml`
**Run:** <https://github.com/ormastes/simple/actions/runs/33357844564>
**Head:** `21bf278fd7eeee85d6fc0558bac09f5bd85a9ef7` (PR #148)

## Summary

**Every job in this workflow failed, including `Native — Linux x86_64`.** That
is the strongest available evidence that CI currently protects nothing: the
host-native lane — the one platform every contributor and every pre-push guard
actually builds on — is red for a reason unrelated to any recent change.

| job | id | conclusion | cause |
|---|---|---|---|
| Native — FreeBSD x86_64 | 99383303457 | failure | **C** (fixed) |
| Cross — Windows x86_64 (MinGW) | 99383303612 | failure | **D** |
| Native — Windows x86_64 | 99383303623 / 626 / 780 | failure | **A** |
| Native — macOS aarch64 | 99383303655 | failure | **C** + **E** (fixed) |
| Native — macOS x86_64 | 99383303662 | cancelled | — |
| Cross — Linux aarch64 | 99383303687 | failure | (not yet triaged) |
| Native — Linux x86_64 | 99383303714 | failure | **B** |
| Cross — Linux riscv64 | 99383303715 | failure | (not yet triaged) |

Causes **C** (E0617 `mode_t` variadic) and **E** (Apple `st_mtimespec`) are fixed
and documented in
`ci_red_on_every_branch_untracked_bin_simple_and_apple_libc_fields_2026-08-31.md`.
That single one-line E0617 fix is FreeBSD's *only* error, so that lane should go
green; macOS needed both. The three below remain open.

---

## Cause A — Windows MSVC: C runtime includes POSIX headers unconditionally

Job 99383303623, `Native — Windows x86_64`:

```
error: failed to run custom build command for `simple-runtime v0.1.0
       (D:\a\simple\simple\src\compiler_rust\runtime)`
  D:\a\simple\simple\src\compiler_rust\runtime\../../runtime\startup/common/runtime_log_hosted.c(18):
  fatal error C1083: Cannot open include file: 'unistd.h': No such file or directory
```

**Real code defect**, not infra. `src/runtime/startup/common/runtime_log_hosted.c`
includes `<unistd.h>` with no platform guard; MSVC has no such header.

**Not a one-line fix, and should not be treated as one.** Adding a
`#ifdef _WIN32` guard around the include will simply surface the next missing
POSIX symbol (`write`, `close`, `ftruncate`, …) — the same "fix one, reveal the
next" pattern macOS just went through twice. The file needs a genuine Win32
backend or an explicit, recorded decision that MSVC is unsupported for this
translation unit.

**Guard gap:** `scripts/check/check-c-runtime-compiles-push.shs` runs
`$CC -fsyntax-only` with the **host** compiler only, so a file that is
well-formed under clang/glibc and impossible under MSVC passes it. The guard's
own three-way classification would call `unistd.h` an unavailable-external-header
SKIP on a Windows host — never a FAIL — so even running it there would not catch
this.

## Cause B — Native Linux x86_64: missing `libfreetype` on the runner

Job 99383303714 — **the host-native lane**:

```
= note: rust-lld: error: unable to find library -lfreetype
        collect2: error: ld returned 1 exit status
error: could not compile ... (exit code 101)
```

**Infra, not code.** The runner lacks the freetype development package. The job
installs no system dependencies before building a target that links it.

**Candidate fix:** add `sudo apt-get update && sudo apt-get install -y
libfreetype6-dev` (likely also `libfontconfig1-dev`) to that job, or gate the
freetype-linking feature off for this lane. Deliberately **not** applied here:
the correct dependency set for this lane belongs to whoever owns the font/render
stack, and guessing risks either an incomplete list or silently disabling a
feature the lane is meant to exercise. Should be a fast fix for that owner.

This is the single most damaging entry in the table — it means the platform
everyone develops on does not build in CI.

## Cause D — Cross MinGW: rustup target not installed

Job 99383303612:

```
error[E0463]: can't find crate for `core`
error[E0463]: can't find crate for `std`
```

**Infra.** Classic missing cross target. The job invokes
`--target x86_64-pc-windows-gnu` without a
`rustup target add x86_64-pc-windows-gnu` step (and needs the MinGW toolchain,
`gcc-mingw-w64-x86-64`, for linking). Low-risk fix, but left to the workflow
owner to apply alongside Cause B, since both are edits to the same job matrix.

## Not yet triaged

`Cross — Linux aarch64` (99383303687) and `Cross — Linux riscv64` (99383303715)
failed but were not investigated in this pass; they are plausibly the same
missing-cross-target class as Cause D.

## Pre-existence

None of these are caused by PR #148: its 11 commits touch zero files under
`bin/` or `.github/`, and causes C and E were verified present verbatim at
`origin/main` (`28ca075c2c7`) — see the sibling record. Causes A, B and D are
properties of the runner environment and of `src/runtime` C source that PR #148
does not modify.

## Cross-cutting guard gap

Both `check-seed-builds-push.shs` (Rust) and
`check-c-runtime-compiles-push.shs` (C) are **host-target-only**. Neither can
observe a break that exists solely under a non-host `#[cfg]` arm or a non-host
C toolchain, which is exactly how macOS-, Windows- and BSD-only breaks reach
`main` with every pre-push guard green. Until a cross-target `cargo check` lane
exists (viable for `#[cfg]`-heavy modules — a scoped probe crate type-checks
cleanly for `aarch64-apple-darwin` and `x86_64-unknown-freebsd` on this Linux
host, though a full-crate check is blocked by `ring`'s SDK-dependent build
script), this workflow is the *only* thing standing between a
non-host compile break and `main` — and it must therefore be kept green rather
than routinely ignored.

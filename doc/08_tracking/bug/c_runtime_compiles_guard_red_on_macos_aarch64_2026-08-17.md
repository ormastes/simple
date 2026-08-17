# `check-c-runtime-compiles-push.shs` is RED on origin/main when run on macOS aarch64

## FIXED — 2026-08-17

Commit `a91c8282dc` restores the mandatory guard on macOS aarch64 without
weakening its failure policy. The checker parses `hosted_cocoa.c` as
Objective-C on Darwin; the AArch64 SIMD path no longer emits the invalid
zero-shift NEON intrinsic; the SciLib probes request Darwin's native extension
surface; and the receiver-valid selfcheck uses a portable mutex/condition
rendezvous instead of optional POSIX barriers.

Measured on macOS aarch64 after the fix:

```text
PASS — 101 file(s) compiled, 0 errors, 5 external-SDK skips
```

The five skips remain the checker's pre-existing explicit unavailable-SDK
category; none of the five files named by this bug are skipped.

- Date: 2026-08-17
- Area: infra / pre-push guards / runtime portability
- Severity: medium — the guard is MANDATORY per `.claude/rules/vcs.md`, and it
  cannot currently return PASS on this host for ANY commit, including origin's
  own tip. That makes it un-actionable here: every landing must reason around
  it, which is exactly how a mandatory guard decays into an advisory one.
- Found by: `.spipe/simple_enterprise_suite` lane W14 landing

## Symptom

Run on macOS aarch64 (Darwin 25.5.0, Apple clang), against a clean worktree
materialised at **origin/main itself** (`06dc5f66b179`), not the shared
working copy:

```
FAIL — 5 file(s) failed to compile: src/runtime/hosted_cocoa.c
  src/runtime/runtime_simd_dispatch.c src/runtime/scilib/accelerator_perf_smoke.c
  src/runtime/scilib/runtime_shim_smoke.c
  src/runtime/test/rt_struct_receiver_valid_selfcheck.c
  (96 compiled clean, 5 skipped for unavailable external dependencies)
```

The identical 5 failures appear at a candidate tip that changes **zero** `.c`
or `.h` files (`git diff --name-only <base> <tip> | grep -cE '\.(c|h)$'` = 0),
which is what establishes them as pre-existing rather than introduced.

## Root cause (at least for one file, confirmed)

`src/runtime/test/rt_struct_receiver_valid_selfcheck.c:23` uses
`pthread_barrier_t`:

```
error: unknown type name 'pthread_barrier_t'; did you mean 'pthread_attr_t'?
```

**macOS does not implement POSIX barriers.** `pthread_barrier_t` /
`pthread_barrier_init` / `pthread_barrier_wait` are part of the optional
`_POSIX_BARRIERS` option, which Apple's libpthread does not provide. This is a
portability gap in the source, not a broken toolchain: the file compiles on
Linux and cannot compile on macOS as written.

The other four were not individually root-caused in this pass. `hosted_cocoa.c`
is macOS-specific by name and is a likelier candidate for a genuine local
defect than the portability class; `runtime_simd_dispatch.c` and the two
`scilib/*_smoke.c` files should be triaged separately.

## Why it matters

`.claude/rules/vcs.md` promoted this guard to MANDATORY on 2026-08-11
specifically because it is the first guard that runs a compiler — the other
six are text-and-tree checks that pass on source which is complete nonsense to
a compiler. That reasoning is sound and this report is **not** an argument for
relaxing it.

But the guard checks a TREE, not a range, and it has no host axis. On a host
where the tree cannot compile for reasons unrelated to the commit under test,
the guard returns FAIL for every possible commit. Its own doc anticipates the
neighbouring case — a missing EXTERNAL header is a SKIP, because "an external
SDK is not installed here" is not evidence of a defect — but a platform that
genuinely lacks a POSIX optional feature is currently classified as a hard
FAIL.

## What was done for the landing

The landing that found this changed zero C files, and the guard returns the
same 5 failures at BASE and at NEW in isolated worktrees. That is the only
honest basis on which it was stepped over, and it is recorded here rather than
left implicit. **This is not a precedent for stepping over a C-runtime FAIL in
general**: any range that touches `src/runtime/**` must return the guard to
green rather than compare failure lists.

## Suggested fix

1. Fix the portability gap directly: guard the barrier code in
   `rt_struct_receiver_valid_selfcheck.c` behind `_POSIX_BARRIERS` /
   `!defined(__APPLE__)`, or supply a small barrier shim built from a mutex +
   condition variable (the usual macOS workaround). Prefer the shim if the
   selfcheck's coverage is meant to hold on every host.
2. Root-cause the remaining four; `hosted_cocoa.c` first, since a macOS-only
   file failing on macOS is the least likely to be a portability artifact.
3. Give the guard a host axis so it stays fail-closed without being
   un-actionable: a file that fails ONLY because the platform lacks a POSIX
   optional feature should be reported in its own category (like the existing
   external-dependency SKIP) — never counted as compiled, never silently
   passed, but distinguishable from a real defect. Until then the guard cannot
   reach PASS on macOS and every landing from this host has to reason around
   it manually.

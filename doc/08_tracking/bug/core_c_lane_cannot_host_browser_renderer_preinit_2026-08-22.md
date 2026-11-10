# core-C lane cannot host the browser renderer worker (preinit constructor compiled out)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** FIXED 2026-11-11 (p3-boot11 lane) — explicit startup entry
`rt_browser_renderer_preinit_enter()` added and called from the generated
native entry main; new selfcheck + runner coverage. Core-C lane can now host
the renderer worker without a constructor. Details in the 2026-11-11
triage section below.
**Filed:** 2026-08-22 (seed lane)

## What changed

`src/runtime/runtime_process.c` registers `browser_renderer_preinit` through a
`.preinit_array` entry so the renderer worker (`argv[0] == "simple-browser-renderer"`)
enters its namespace/landlock/seccomp jail before `main`. The Stage4 archive-core
contract (`native_project/tools.rs::forbidden_archive_sections`, matched by
`archive_definition_owners` and the capsule projection) rejects every
constructor/destructor section in the core archive, and `.preinit_array` is
one — `test_stage4_runtime_capsule_keeps_only_requested_globals` failed with
`Stage4 archive core retained constructor/destructor sections: .init_array`
(substring match on `.preinit_array`).

The registration is now inside `#if !defined(SIMPLE_CORE_C_STANDALONE)`. The
function itself still compiles everywhere (the selfchecks that call it directly
still link).

## Why this is fail-closed

`rt_browser_renderer_sandbox_enter()` (`runtime_process.c`) refuses unless
`s_browser_renderer_preinit_active` was set by the preinit hook, and
`src/os/hosted/hosted_browser_renderer_worker.spl:1270` exits when
`browser_renderer_sandbox_enter()` is false. A renderer worker built on the
core-C standalone lane therefore **refuses to run**; it never runs unjailed.

## What is actually missing

An explicit startup entry, e.g. `rt_browser_renderer_preinit_enter(argc, argv, envp)`
callable from the worker's generated `main` (the core-C entry shim would need
to forward `argc/argv/envp`), so the jail can be entered without a constructor.
Until then the renderer worker must be built on a lane that keeps `.preinit_array`
(the non-standalone bundle in `src/compiler/70.backend/backend/runtime_compiler.spl`).

## Options

1. Add the explicit entry + have the core-C `main` shim call it for the worker
   marker. Keeps Stage4's no-constructor invariant.
2. Allow `.preinit_array` specifically in `forbidden_archive_sections`. Weakens
   the invariant the Stage4 tests exist to prove; not recommended.



## Triage 2026-11-10 (p3-boot4 lane, assignment row 26)

**Verdict: LIVE — fix blocked by this lane's scope.**

Re-verified at this lane's base (origin/release/1.0.0); the requested
explicit startup entry was never added:

- No `rt_browser_renderer_preinit_enter` (or any explicit preinit entry)
  exists anywhere under `src/runtime/` (grep 2026-11-10, zero hits).
- `src/runtime/runtime_process.c:3844-3853` still compiles the
  `.preinit_array` registration out under `#if !defined(SIMPLE_CORE_C_STANDALONE)`
  and keeps only an unreferenced-for-production alias in the standalone arm;
  the source comment at `:3834-3843` still cites this bug as the recorded
  open state.
- Consequence unchanged: a core-C-standalone-built renderer worker still
  fails closed (`rt_browser_renderer_sandbox_enter()` refuses without
  `s_browser_renderer_preinit_active`; worker exits).

The documented fix (doc option 1: add `rt_browser_renderer_preinit_enter(argc,
argv, envp)` and have the core-C entry shim forward `argc/argv/envp` for the
worker marker) requires edits to `src/runtime/runtime_process.c` **and** the
compiler-generated core-C main shim (`src/compiler` backend). Both trees are
outside this lane's scope (`src/runtime` runtime lane; `src/compiler`
seed-fix lane active). No change made in this lane; fix sketch above is
ready for whichever lane owns those trees.

## Triage 2026-11-11 (P3 boot11 lane, work/p3-boot11-20261111)

**Verdict: FIXED in this lane — doc option 1 implemented (explicit startup
entry + entry-shim forwarding), paired with a selfcheck and runner coverage.**

Change (option 1; option 2's invariant-weakening rejected as recommended):

- `src/runtime/runtime_process.c`:
  - New exported `rt_browser_renderer_preinit_enter(argc, argv, envp)` in the
    Linux arm, forwarding to `browser_renderer_preinit()` — the same jail the
    `.preinit_array` constructor entered.
  - No-op stubs in the non-Linux POSIX arm and the Windows arm, so the
    runtime.h symbol resolves on every lane (the jail itself is Linux-only).
  - `browser_renderer_preinit()` made idempotent (early return once
    `s_browser_renderer_preinit_active`): the hosted lane keeps the
    constructor, which now runs BEFORE the entry call, so the entry call must
    not re-enter namespaces/Landlock/seccomp (a double-enter would
    `_exit(126)` the already-jailed worker).
  - Standalone-arm comment updated; the "what is missing" comment now records
    the explicit entry as the documented way out.
- `src/runtime/runtime.h`: declaration beside the other
  `rt_browser_renderer_*` process symbols.
- `src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl`
  (`compile_entry_point_c`, the entry generator used by the pure-Simple
  native link, including the core-C standalone lane): the generated
  `main(argc, argv)` now calls `rt_browser_renderer_preinit_enter(argc, argv,
  environ)` as its first statement under `#if !defined(_WIN32)`, before
  `spl_init_args`/`__simple_runtime_init` — matching the constructor's
  before-main ordering. The callee is a no-op for any argv[0] that is not
  `simple-browser-renderer`, so ordinary binaries are unaffected. Stage4
  capsule liveness needs no static list change: `stage4_live_runtime_requests`
  derives requested symbols from the link closure's undefined symbols.
  (The Rust-seed linker's own Stage4 main stub in
  `native_project/linker.rs` was NOT touched; seed-built workers still get
  the constructor. Symmetric coverage there is a follow-up for a lane that
  may run cargo.)
- Test pairing: new selfcheck
  `src/runtime/test/rt_browser_renderer_preinit_entry_selfcheck.c`
  (REQ-WEB-BROWSER-014) — Arm 1: the exported entry forwards the worker
  marker into the real preinit (non-empty envp must `_exit(126)`; catches
  the fail-open "wrapper became a stub" shape); Arm 2: ordinary argv passes
  through untouched with `sandbox_enter()` still refusing. Wired into
  `scripts/check/check-browser-renderer-sandbox-seccomp.shs` (+2 counted
  assertions, no vacuity).

Verification run 2026-11-11 on this Windows lane:

- `cc -fsyntax-only` (llvm-mingw) of `runtime_process.c`, with and without
  `-DSIMPLE_CORE_C_STANDALONE=1` — clean (exercises the Windows arm incl. the
  new stub).
- New selfcheck + sibling startup-failure selfcheck build clean under MinGW
  and print their documented `SKIP (linux only)` / exit 77 (jail is
  Linux-only; the Linux CI gate runs both arms for real).
- `simple lint src/compiler/70.backend/backend/llvm_native_link_hosted_support.spl`
  (seed-smoke, fresh seed 46fe8f6b6def) — 0 errors; none of the 5 warnings
  touch the edited region. (Standalone `simple compile` of that module fails
  identically at the unmodified base — pre-existing package-context
  constraint, not a regression of this change.)
- The exact generated-entry C snippet compiled `-Wall -Wextra` clean in both
  the POSIX branch (`-U_WIN32`) and the `_WIN32` branch.

Honest gap: the Linux arm of the C change (wrapper + idempotency) and the
end-to-end core-C renderer-worker link could not be compiled/run on this
Windows host; first full compile+run of those arms happens on the Linux CI
gate (`check-browser-renderer-sandbox-seccomp.shs`).

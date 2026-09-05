# core-C lane cannot host the browser renderer worker (preinit constructor compiled out)

**Status:** OPEN — fail-closed gap, not a silent one
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

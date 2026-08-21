# browser_renderer_apply_namespaces / browser_renderer_drop_privileges never implemented

- Date: 2026-08-21
- Found via: `sh scripts/check/check-c-runtime-compiles-push.shs` (the mandatory
  C-runtime-compiles pre-push guard, see `.claude/rules/vcs.md`), which reported
  the sole pre-existing failure in the tree:
  `src/runtime/test/rt_browser_renderer_namespace_selfcheck.c:55,57` —
  undeclared identifiers `browser_renderer_apply_namespaces` and
  `browser_renderer_drop_privileges`. Reproduces identically on clang-20 and
  clang-23.

## Evidence

`grep -rn 'browser_renderer_apply_namespaces\|browser_renderer_drop_privileges' src/runtime src/lib examples`
returns matches only inside the selfcheck file itself (its header comment and
the two call sites at lines 55/57) — there is no definition, declaration, or
any other reference anywhere else in `src/runtime`, `src/lib`, or `examples`.

`src/runtime/runtime_process.c` (which the selfcheck `#include`s directly) does
implement a related sandbox entry point, `rt_browser_renderer_sandbox_enter`
(line 2048/2067, two variants), which internally calls
`browser_renderer_set_limit`, `browser_renderer_apply_landlock`, and
`browser_renderer_apply_seccomp` — but none of these is
`browser_renderer_apply_namespaces` or `browser_renderer_drop_privileges`. The
namespace-isolation and privilege-drop behavior the selfcheck's comment block
describes (network-namespace `unshare`, irreversible `setuid(0)` drop) does not
exist in the runtime.

## Root cause

The selfcheck (`src/runtime/test/rt_browser_renderer_namespace_selfcheck.c`,
added per `doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md`
as "Phase 2 of the sandbox model") was written ahead of the implementation and
the implementation never landed. The file was left calling two functions that
were never written, which is invisible to every guard except one that actually
compiles the file (`check-c-runtime-compiles-push.shs`'s `-fsyntax-only` scan).

## Fix applied (this change)

Per CLAUDE.md ("NEVER convert TODO to NOTE - implement or delete... implement
nothing" is not license to silently stub): rather than fabricate a fake
implementation of a security-sensitive privilege-drop/namespace-isolation path,
the selfcheck now fails LOUDLY at compile time via
`#error` guarded by `#ifndef SPL_HAS_BROWSER_RENDERER_NAMESPACES`, naming this
bug record. This makes the gap a hard, visible compile failure instead of an
undeclared-identifier warning-turned-error, and keeps
`check-c-runtime-compiles-push.shs` from reporting a false PASS once this file
compiles again — it will need `SPL_HAS_BROWSER_RENDERER_NAMESPACES` defined
(and the two functions actually implemented in `runtime_process.c`, and the
selfcheck's calls left as-is) before it can compile.

## Follow-up (not done here, out of scope for this change)

Implement `browser_renderer_apply_namespaces()` (network-namespace `unshare` +
`/proc/self/ns/net` verification) and `browser_renderer_drop_privileges()`
(irreversible privilege drop) in `src/runtime/runtime_process.c`, following the
same order the selfcheck's own comment documents (namespaces before privilege
drop, since dropping privileges first would remove the `CAP_SYS_ADMIN` needed
for the namespace call). Then define `SPL_HAS_BROWSER_RENDERER_NAMESPACES` and
re-verify.

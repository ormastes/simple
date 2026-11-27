# Seed resolver: `x.is_none()` resolves to a PRIVATE free `fn is_none<T>` in an unrelated module (2026-11-22)

Status:
- Resolver defect: OPEN (seed resolver owner). Not fixed here.
- Workaround applied: the unused helper in `outline_members.spl` is deleted, so the trigger is
  gone. It carries no `@workaround` marker because no code remains to mark. This record is the link.

## Symptom (exact)

New Phase 1 seed (release `6816f70c47e`), `scripts/check/check-simple-core-runtime-smoke.shs`.
The simple-core archive was produced. The first smoke step,
`native-build --runtime-bundle simple-core --entry examples/01_getting_started/hello_native.spl`,
failed with:

```
error: semantic: private fn `is_none` of module `//?/D:/dev/simple/.claude/worktrees/agent-afe37bcfe31bb957f/src/compiler/10.frontend/treesitter/outline_members.spl` is not visible to //?/D:/dev/simple/.claude/worktrees/agent-afe37bcfe31bb957f/src/compiler/80.driver/driver_hir_cache.spl; mark it `pub` or `export` it
  interpreter: D:/dev/simple/.claude/worktrees/agent-afe37bcfe31bb957f/build/essential-apps/p1n-seed/simple.exe (exit code 1)
```

The script exited 1 under `set -e` with no verdict line. The build log was in
`/tmp/simple_core_hello_build.<pid>`.

## Files

- Callee, module B: `src/compiler/10.frontend/treesitter/outline_members.spl:41` (before this
  change) declared `fn is_none<T>(v: T) -> bool: v == nil`. It was private and had no callers.
- Caller, module A: `src/compiler/80.driver/driver_hir_cache.spl` makes method calls
  `thir_constraints.is_none()`, `src_opt.is_none()`, `source_digest_opt.is_none()`,
  `loaded.is_none()` and `decoded.is_none()` at lines 358, 364, 403, 531 and 633. A does not
  import B.

## Defect

The seed resolved the method call `x.is_none()` in A to a free function from another module,
and a private one at that. Visibility checking then rejected it. Method-call resolution must
not consider free functions from other modules, and must never consider private ones. The
Option method should have been chosen.

## Minimal repro sketch

```
# B.spl
fn is_none<T>(x: T?) -> bool:      # private
    x == nil
pub fn b_marker() -> i64: 7

# A.spl
use <B>.{b_marker}
fn main() -> i64:
    val v: i64? = nil
    if v.is_none(): print "ok"
    0
```

Measured 2026-11-22: this two-module form does NOT reproduce under the old Phase 1 seed's
direct interpreter. `simple.exe run main.spl` printed the Option-method result. The failure was
observed only when the seed interprets the pure-Simple compiler driver during `native-build`,
with B co-compiled in the large `src/compiler` closure and not imported by A. Reproducing it
cheaply needs that closure shape, or the native-build "co-compiled definitions" resolution
path, so no failing spec was added.

## Unblock condition

Restrict UFCS and free-function fallback for method calls to visible, imported or prelude
functions in the seed resolver. Add a spec with B co-compiled but not imported by A.

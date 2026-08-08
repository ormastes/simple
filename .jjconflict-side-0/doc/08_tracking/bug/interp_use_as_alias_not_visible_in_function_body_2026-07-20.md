# Bug: module-level `use <module> as <alias>` binding not resolvable when referenced inside a function/method body — "variable `<alias>` not found"

- **Date:** 2026-07-20
- **Status:** open
- **Area:** interpreter/semantic name resolution for aliased module imports. Reproduced in two independent files:
  - `src/compiler/90.tools/verify/checker.spl:8` (`use verification.regenerate as regen`), used inside top-level `fn known_verification_files()` at line 130
  - `src/compiler_rust/lib/std/src/verification/toolchain.spl:8` (`use host.process as process`), used inside `class ToolchainInfo`'s `static fn detect()` at line 30
- **Binary:** reproduced on `bin/release/x86_64-unknown-linux-gnu/simple`, which currently prints the Rust-seed bootstrap warning (`WARNING: this Rust-built Simple binary is a bootstrap seed only`) — **this is likely a seed-interpreter landmine**, not necessarily present in a genuinely self-hosted pure-Simple build. Not independently re-verified there (task scope excluded rebuilding/bootstrapping).
- **Related:** `doc/08_tracking/bug/interp_module_alias_time_shadowed_builtin_2026-07-02.md` documents a narrower instance of what may be the same family — `use X as time` fails because the alias name collides with a builtin/reserved name. This report's evidence is broader: the alias names here (`regen`, `process`) are not obviously builtin/reserved, and the failure specifically correlates with the reference site being **inside a function/method body** rather than top-level module code, which the `time` doc did not establish either way.

## Symptom

`tool_checker_spec.spl`, example "uses the authoritative Lean artifact list":
```
semantic: variable `regen` not found
```
from `checker.known_verification_files()`, whose entire body is:
```simple
fn known_verification_files() -> [text]:
    regen.known_regenerated_files()
```
with `use verification.regenerate as regen` at module top level (checker.spl:8).

`toolchain_detection_spec.spl`, 4 examples ("detects whether Lean is available", "reports version_match true when no lean-toolchain file and lean is available", "produces a non-empty format_status", "returns ProjectInvalid for nonexistent directory"):
```
semantic: variable `process` not found
```
from `ToolchainInfo.detect()`, which calls `process.run("lean", ["--version"])` (toolchain.spl:30), with `use host.process as process` at module top level (toolchain.spl:8).

In both cases the alias is declared correctly at module scope and the module it points to exists; the alias is simply not visible from inside a `fn`/`static fn` body in the same file.

## Impact

Any `.spl` file that imports a module under an alias (`use X as Y`) and then references that alias from inside a function or method body — rather than only at top-level statements — fails at runtime with a spurious "variable not found," even though the exact same alias declaration is syntactically valid and (per `src/compiler/90.tools/verify/main.spl:11`, which uses `import verification.regenerate as regen` — the `import` keyword, not `use`) a same-target import under a different keyword may behave differently. This affects at least the tool_checker and toolchain-detection code paths in the formal-verification test section; the pattern (aliased module import + function-scoped use) is common enough elsewhere in the codebase that this may have broader reach beyond the two reproductions here.

## Suggested fix direction

Confirm whether `use MODULE as ALIAS` bindings are supposed to be visible for the whole file (as `import MODULE as ALIAS` apparently is, based on `main.spl`'s working sibling usage) and, if so, fix alias-binding scope so it is captured by nested function/method closures the same way un-aliased `use` imports already are. If `use ... as` is intentionally file-scope-only for some reason, `checker.spl` and `toolchain.spl` need to switch to `import ... as` instead — but that would be a source-level workaround, not a fix for the underlying scoping asymmetry.

## Repro

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/00_formal_verification/compiler/tool_checker_spec.spl --no-session-daemon
bin/release/x86_64-unknown-linux-gnu/simple test test/00_formal_verification/compiler/toolchain_detection_spec.spl --no-session-daemon
```

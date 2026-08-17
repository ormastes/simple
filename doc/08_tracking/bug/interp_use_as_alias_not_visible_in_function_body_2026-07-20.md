# Bug: module-level `use <module> as <alias>` binding not resolvable when referenced inside a function/method body — "variable `<alias>` not found"

- **Date:** 2026-07-20
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
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

---

## Verification 2026-08-17 (compiler-lint lane) — the SCOPING claim does NOT reproduce; a different, real defect is underneath

### Source unchanged

`src/compiler/90.tools/verify/checker.spl:9` still reads `use verification.regenerate as regen`,
and `known_verification_files()` at `checker.spl:131-132` still has the one-line
body `regen.known_regenerated_files()`. So the occurrence this record describes
is still present in source; nothing was silently refactored away.

### Minimal fixture — the interpreter resolves the alias in a function body FINE

Two-file fixture, alias declared at module scope, referenced BOTH at top level
and inside a `fn` body:

```
# helper.spl
fn helper_value() -> i64:
    7

# main.spl
use helper as h

fn from_body() -> i64:
    h.helper_value()

fn main():
    val top = h.helper_value()
    print("top={top}")
    print("body={from_body()}")
```

```
$ nice -n 19 bin/simple run .../main.spl
[CODEGEN BODY] Function 'from_body' body compilation failed: GlobalLoad: unresolved identifier 'h' (not a global, function, const-data name, or import)
[CODEGEN BODY] Function 'main'      body compilation failed: GlobalLoad: unresolved identifier 'h' (not a global, function, const-data name, or import)
[INFO] JIT compilation failed, falling back to interpreter: ... 2 function body/bodies failed to compile: [from_body, main]
top=7
body=7
```

Both values are **7**. The alias is visible inside the function body and yields
the right answer. So the title's claim — *"module-level `use <module> as <alias>`
binding not resolvable when referenced inside a function/method body"* — is
**refuted as stated** for the interpreter.

### What is actually broken, and it is NOT scope-dependent

The JIT/codegen path cannot resolve an aliased module import **at all**:
`GlobalLoad: unresolved identifier 'h'` fires for `main` (a *top-level* reference)
exactly as it does for `from_body`. Function-body position is irrelevant; the
correlation this record drew with "inside a fn body" is not real. The engine then
falls back to the interpreter and produces the correct result, so today this is a
silent **performance** cliff (every `use ... as` module drops out of JIT), not a
wrong answer.

Control, to show the error is specific and not a generic module failure — an
alias to a genuinely missing module produces a *different* diagnostic:

```
$ bin/simple run .../missing.spl        # use nonexistent.module.path as nx
[WARN] Failed to load imported types ... E1034 cannot resolve import: module path segment `nonexistent` not found
error: semantic: Cannot resolve module: nonexistent.module.path
```

`Cannot resolve module: ...`, **not** `variable 'nx' not found`. So the symptom
this record quotes (`semantic: variable 'regen' not found`) is neither the
missing-module shape nor the working-alias shape reproduced above.

### Likely real cause of the ORIGINAL symptom (not proven)

`verification.regenerate` does not live under `src/lib/`. It resolves only from
`src/compiler_rust/lib/std/src/verification/regenerate/`, a *different* stdlib
root. Whether that root is on the module search path depends on how the process
was launched, which would explain why the failure appeared under the spec runner
and not under `run`. Same story for `use host.process as process` — a `host`
package exists nowhere in owned `src/**` (`find src -path '*host/process*'`
returns only the unrelated `src/app/wm_compare_host/process_ops.spl`).

**Verdict: the alias-scoping defect as filed is UNVERIFIED and its stated
mechanism is refuted.** Two follow-ups, neither in this lane's scope:

1. **Real, reproducible, and worth its own row:** aliased module imports are
   unresolvable in JIT codegen (`GlobalLoad: unresolved identifier '<alias>'`),
   silently demoting the module to the interpreter. Owner: the codegen/backend
   lane.
2. Re-file the original symptom as a **module-search-path** question about the
   `src/compiler_rust/lib/std/src` root under the spec runner, not as alias
   scoping.

Not proven: this lane did not obtain a `Results:` line from
`test/00_formal_verification/compiler/tool_checker_spec.spl`. The run was
launched under `scripts/resource/test-slot.shs` with `--timeout 900` and
produced **zero bytes of output** for over 40 minutes at host load 48-124 with
~104 concurrent `simple test` processes (the `--timeout 900` never fired). It
was then deliberately SIGTERMed by this lane to free a test slot on a host
running a priority bootstrap, so it exited **rc=144 — that exit code is this
lane's own kill, NOT a test failure**. Per the session-brief rule, an absent
`Results:` line is UNVERIFIED: not a pass and not a failure.

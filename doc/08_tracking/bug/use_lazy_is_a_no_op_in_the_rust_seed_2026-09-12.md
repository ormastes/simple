# `use lazy` is accepted and silently loaded eagerly by the deployed seed

- Status: OPEN (2026-09-12)
- Binary: deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`,
  sha256 `3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef`

## Symptom

`use lazy <module>.{...}` parses, type-checks and runs, and defers nothing.
The module and its whole transitive closure are loaded exactly as an eager
`use` would load them, with no diagnostic.

Deterministic proof, `src/app/cli/lint_entry.spl` with its implementation
import spelled both ways, counting `.spl` opens under
`strace -f -e trace=openat` for `bin/simple lint --help`:

| spelling | `.spl` opens |
|---|---:|
| `use app.io.cli_lint_commands.{...}` | 1,532 |
| `use lazy app.io.cli_lint_commands.{...}` | **1,532** |

Byte-identical. An interleaved wall-clock A/B over three repetitions
(eager 3,794 / 5,004 / 3,974 ms vs lazy 4,471 / 3,775 / 5,825 ms) shows no
signal either — the difference is entirely box noise.

## Cause

`src/compiler_rust/compiler/src/interpreter_module/module_evaluator/evaluation_helpers.rs:575`

```rust
// Note: `use lazy` is parsed but loaded eagerly in the Rust bootstrap interpreter.
// Actual lazy/deferred loading is implemented in the Simple interpreter
// (src/compiler/10.frontend/core/interpreter/eval_stmts.spl).
if use_stmt.is_lazy {
    trace!("Loading lazy import eagerly (Rust bootstrap): {:?}", use_stmt.path);
}
```

This is a known and deliberate bootstrap limitation. It is filed because it is
invisible at the call site: production code has already been written against the
keyword as if it worked. `src/app/io/cli_lint_commands.spl` spells three of its
imports `use lazy` (lines 6, 11, 12 — the formatter, the fix tool and the fix
rules) while `simple fmt --help` still pays the full lint + compiler-frontend
closure, because none of those three are actually deferred on the deployed
binary.

## Why it matters

`use lazy` is the sanctioned mechanism for keeping a CLI entry point thin, and
is the first thing an author reaches for when fixing
`subcommand_help_loads_implementation_closure_2026-09-12.md`. On the deployed
seed it silently buys nothing, so the perf defect it is meant to fix survives a
change that looks correct in review.

## Suggested fix

Either implement deferred loading in the seed (defer `load_and_merge_module`
until the first unresolved lookup of one of the imported names), or — if that
stays out of scope for the bootstrap — emit a one-line warning when `is_lazy`
is seen, so an author is told the keyword is inert on this binary instead of
discovering it with strace.

## Repro

```sh
cnt() { strace -f -e trace=openat -o /tmp/tr bin/simple lint --help >/dev/null 2>&1
        grep -c '\.spl"' /tmp/tr; }
cnt                                              # eager spelling
sed -i 's/^use app.io.cli_lint_commands/use lazy app.io.cli_lint_commands/' \
    src/app/cli/lint_entry.spl
cnt                                              # identical count
```

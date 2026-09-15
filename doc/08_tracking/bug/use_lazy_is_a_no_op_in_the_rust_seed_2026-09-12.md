# `use lazy` is accepted and silently loaded eagerly by the deployed seed

- Status: OPEN (re-confirmed 2026-09-13 at `f26970e9d93`; the blocker is now
  identified and is architectural, see "Why the seed cannot simply defer")
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

## Re-confirmed and bounded (2026-09-13)

Reproduced on this tree at `f26970e9d93`, same binary, with a two-line probe
that imports `app.io.cli_lint_commands` and never calls it:

| spelling | `.spl` opens | wall |
|---|---:|---:|
| `use app.io.cli_lint_commands.{run_lint_command}` | 1,109 | 6,386 ms |
| `use lazy app.io.cli_lint_commands.{run_lint_command}` | **1,109** | 5,058 ms |

Byte-identical open counts; the wall difference is box noise (load ~40).

## The other lane already implements it

This is not a missing design, it is a missing seed implementation. The
pure-Simple interpreter defers properly:

- `src/compiler/10.frontend/core/interpreter/eval_decls.spl:136` — a `DECL_USE`
  whose `decl_get_is_lazy(did) == 1` calls
  `register_deferred_module(module_path, current_file, imported_names)` and
  returns, loading nothing;
- `src/compiler/10.frontend/core/interpreter/module_loader_core.spl:120-172` —
  the deferred registry, `force_deferred_module` and
  `try_force_any_deferred_for(symbol)`, which materializes a deferred module on
  the first unresolved lookup of one of its names;
- `src/compiler/10.frontend/core/interpreter/module_loader_lazy.spl` — the
  outline-first loader that bridges into the same mechanism.

## Why the seed cannot simply defer

The seed's `use lazy` arm at `evaluation_helpers.rs:575` is not where the cost
is. `simple lint --help` takes `exec_core.rs::run_file_jit`, which calls
`simple_compiler::pipeline::module_loader::load_module_with_imports(path, ...)`
and flattens the ENTIRE transitive import closure into one AST before HIR
lowering, MIR and codegen. `is_lazy` is read nowhere in
`pipeline/module_loader.rs` (a repo-wide grep finds it only in the parser, in
HIR `module_lowering` as metadata, and in that one runtime trace call), so the
flatten is what opens the 1,109 files, and the runtime arm sees an
already-loaded closure.

Making the flatten honour `is_lazy` is therefore necessary but not sufficient:
the deferred module's symbols would then be unresolved externals at codegen
time, and the JIT already answers that by dropping the whole module to the
interpreter —

```
[jit-fallback] unresolved external symbol 'run_fmt_command': whole module
dropped to the interpreter (expect ~100-1000x slowdown).
```

— which is the second defect recorded in
`function_local_use_loses_enum_scope_2026-09-12.md` (whose FIRST defect, the
lost enums, was fixed on 2026-09-13; this JIT half was not) and is the same
root. So a
naive seed-side deferral trades a 9.5 s help path for a 100-1000x slower REAL
path. A correct seed implementation needs the deferred load to be able to
re-enter codegen (or the lazy symbols to be called through an indirection the
JIT can link), which is a materially larger change than this lane's budget and
is not attempted here.

## What was done instead

1. `subcommand_help_loads_implementation_closure_2026-09-12.md`, the defect this
   keyword was reached for, is fixed WITHOUT `use lazy`: a help request is
   dispatched to a different, closure-free entry
   (`src/app/cli/tool_help_entry.spl`).
2. The SEMANTICS are pinned on both lanes by
   `test/01_unit/compiler/loader/lazy_use_equivalence_spec.spl`: for the same
   program, the lazy and eager spellings must produce the same output and the
   same exit code, whether or not the imported name is ever used, and the
   pure-Simple deferral path must stay wired. The spec deliberately does NOT pin
   the seed's open counts — freezing the eager behaviour would turn this defect
   into a requirement. It also means a future seed-side deferral has an
   executable definition of "must not change behaviour" to land against.

The record's own alternative suggestion — warn when `is_lazy` is seen — was not
taken: three imports in `src/app/io/cli_lint_commands.spl` are spelled
`use lazy`, so an unconditional warning would add three stderr lines to every
`lint`/`fmt`/`fix` invocation, and a warning behind an env var would be as
invisible as the defect it describes.

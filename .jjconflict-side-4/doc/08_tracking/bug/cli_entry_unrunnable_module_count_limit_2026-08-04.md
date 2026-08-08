# The pure-Simple CLI entry cannot be run at all — 800-module import limit

**Status:** OPEN
**Found:** 2026-08-04
**Severity:** high — `src/app/cli/main.spl` is the pure-Simple CLI entry point
and produces zero output from every invocation; 7 spec examples are red on it

## Symptom

```sh
cd /home/ormastes/dev/pub/simple
SIMPLE_LIB="$PWD/src" SIMPLE_TIMEOUT_SECONDS=0 bin/simple run src/app/cli/main.spl --help
```

Actual: **stdout is empty (0 bytes)**, exit 1. The same holds for the module
that actually defines `fn main`:

```sh
SIMPLE_LIB="$PWD/src" bin/simple run src/app/cli/_CliMain/main_and_help.spl --help
# 0 bytes on stdout, exit 1
```

Expected: the CLI help banner.

`test/02_integration/app/cli_log_modes_spec.spl` is red on exactly this —
`Results: 7 total, 0 passed, 7 failed`, every message of the form
`expected  to contain …` with an **empty** actual:

```
✗ shows shared log options in help                 expected  to contain --progress
✗ supports log-mode json ready output              expected  to contain "status":"ready"
✗ supports log-mode json version output            expected  to contain "version":"
✗ supports dot progress for help output            expected  to contain .
✗ rejects invalid log mode                         expected 0 to equal 1
✗ preserves check presentation options through delegation
✗ rejects split check surface before delegation
```

## Root cause (PROVED)

The failure is on stderr and is a hard runtime error, not a missing `main`:

```
error: runtime: Module count limit (800) exceeded loading
"/home/ormastes/dev/pub/simple/src/app/cli/theme_sync.spl".
Too many transitive imports.
```

`src/app/cli/main.spl` is 18 lines of `export use`, and
`src/app/cli/_CliMain/main_and_help.spl` reaches every subcommand module
eagerly, so the transitive import set crosses the runtime's 800-module ceiling
before `fn main` (`main_and_help.spl:190`) is ever entered. The loader aborts,
nothing is printed, and the exit status is the only signal.

A `[memory-guard]` line fires on the same run
(`SIMPLE_LIB=… contains 600+ .spl files`), and the load also emits ~40
`compiler_cross_module_private_symbol_collision` warnings, so the module graph is
already known to be over-wide — the 800 limit is where it becomes fatal.

## Why not fixed now

Two candidate fixes, neither safe from a test-repair lane:

1. **Raise the limit.** That is a runtime constant guarding real memory
   behaviour, and the guard is doing its job — the import graph genuinely is
   ~800 modules deep for one `--help`. Raising it hides the growth instead of
   bounding it.
2. **Make subcommand loading lazy** (dispatch already owns a table of
   `app_path` strings in `src/app/cli/dispatch/table.spl`, so the entry does not
   need every subcommand module linked in). That is a real restructuring of the
   CLI entry graph, it changes startup behaviour for every command, and it
   overlaps the bootstrap/deployment work that is already in flight.

Note the interaction with the known deployment defect: the currently deployed
`bin/simple` prints "this Rust-built Simple binary is a bootstrap seed only" and
has lost subcommands. Until the pure-Simple CLI entry can load, that gap cannot
be closed from the Simple side either.

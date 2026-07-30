# Stage-3 whole-tree build mis-parses vhdl_codegen_helpers.spl (parser STATE, not grammar)

**Found:** L7 run 9 (2026-07-30), faithful stage-3 invocation on origin
`110f743b2a2`, cranelift, `--entry-closure --mode one-binary`.
**Status:** Open — root cause narrowed to parser/lexer state in whole-tree
(focused) builds. Blocks stage 3, therefore blocks L7 / Stage-4.

Supersedes `stage2_parser_result_unit_generic_divergence_2026-07-29.md`,
whose grammar diagnosis is retracted (see that doc).

## Symptom

45 `[parser_error]` lines, ALL in a single file, reached through the symlink
path spelling:

```
[parser_error] path src/compiler/backend/backend/vhdl_codegen_helpers.spl line 201:13: expected :, got Ident 'arg_exprs'
[parser_error] path .../vhdl_codegen_helpers.spl line 201:13: expected Indent, got Ident 'arg_exprs'
[parser_error] line 202:1: unexpected token in expression: Dedent ''
[parser_error] path .../vhdl_codegen_helpers.spl line 207:122: expected :, got Ident 'CompileError'
[ERROR] phase 4 FAILED
error: focused native-build: parse error in src/compiler/backend/backend/vhdl_codegen_helpers.spl
```

First failure is line 201 (`arg_exprs = arg_exprs.push(arg_expr)`), i.e. the
statement immediately AFTER a `match` block's last arm. The parser was still
expecting another `case … :` and choked on the dedent. Everything after
(including the line-207 signature) is cascade.

## What is NOT the cause — each measured, not inferred

Method: parse with a real stage-2 pure-Simple binary
(`build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build`).

| Candidate | Result |
|---|---|
| `fn f() -> Result<(), text>:` (unit type in generic args) | parses clean, exit 0 |
| `match if c: a else: b:` (inline if as match subject) | parses clean, exit 0 |
| Exact failing block (class + method + `for` + `match if` + `case Err(e): return Err(e)`) | parses clean, exit 0 |
| The ENTIRE victim file, in isolation, @origin | zero `parser_error`; reaches HIR |
| The ENTIRE victim file, in isolation, @run-8 pin `38cb691ad082` | zero `parser_error`; byte-identical to origin |
| Victim parsed after a 400-line pad file (position accumulation) | zero `parser_error` |
| Victim reachable through a symlinked alias directory | zero `parser_error` |
| `SIMPLE_AST_GEN_CHECK=1` stale-generation / OOB diagnostics during the failing run | **0** |

So: the grammar accepts every construct in the file, and the file parses
clean by itself at both trees. The failure exists ONLY in the whole-tree
focused build.

## Leading hypotheses (untested)

1. **Focused/entry-closure partial parse.** Phase 4 is a "focused"
   native-build driven by `--entry-closure`. If focused mode parses a
   SUBSET of a file (only entry-reachable functions), a region sliced
   mid-file would start with the wrong indentation baseline — which matches
   the symptom exactly (`expected Indent`, `unexpected Dedent`, arms not
   terminating).
2. **Double registration via the symlink spelling.** `src/compiler/backend`
   is a symlink to `70.backend`, so the same file is reachable under two
   module names (see memory `reference_compiler_symlink_module_spellings`).
   A second parse reusing first-parse arena/lexer state would corrupt
   block structure. Note the error path uses the SYMLINK spelling, so the
   symlink pass is the one that failed.
3. **Capacity exhaustion in a fixed-size parser side table.** Whole-tree
   parsing fills the named-type / tuple / isolated-type registries that
   `parser_parse_type_impl` consults; a silent overflow would degrade
   parsing only at scale. `tuple_type_register` has an explicit
   `< 0` overflow path, so check the others for silent truncation.

## Repro

```
# fails (~7 min):
cd <worktree at origin>
build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple native-build \
  --target x86_64-unknown-linux-gnu --backend cranelift \
  --runtime-bundle core-c-bootstrap \
  --source src/compiler --source src/app --source src/lib --source examples/10_tooling \
  --entry-closure --low-memory --threads 8 --mode one-binary \
  --entry src/app/cli/main.spl --runtime-path <wt>/src/compiler_rust/target/bootstrap -o /tmp/out.bin

# passes: same binary, same file, isolated source dir
```

`--entry-closure` is required to reproduce the build at all: without it the
multi-root scan aborts earlier on a module-name collision
(`src/app/__init__.spl` and `src/compiler/__init__.spl` both sanitize to
`__init__`) — worth fixing separately, since it makes non-closure whole-tree
builds impossible.

## Next step

Bisect hypothesis 1 first (cheapest, best symptom match): dump the exact
source text the focused path hands the lexer for this module and compare it
byte-for-byte with the file on disk.

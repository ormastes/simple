# PARSE001 makes lint fail open: unparseable files receive ZERO AST lints

Date: 2026-08-08

Status: Fixed (both census hits repaired); census method recorded for reuse

## Summary

`bin/simple lint` reports an unparseable file as:

```
error[PARSE001]: NOT LINTED: source did not parse - every AST-based lint was
skipped for this file (<parser message>)
```

A file in that state receives **no AST-based lints at all**. It contributes zero
findings to a tree-wide lint run and is therefore indistinguishable from a clean
file unless PARSE001 is grepped for explicitly. Any sweep that treated "lint is
green" as evidence about such a file was measuring nothing.

Two distinct root causes were found, and they are **not** the same defect.

## Exit-code behaviour (measured, NOT changed)

The initial suspicion was that lint exits 0 on PARSE001. It does not:

| condition | exit code |
|-----------|-----------|
| any target hits PARSE001 | **1** |
| all targets parse, no errors | **0** |

Measured with an armed sentinel (`cmd > out 2>&1; echo "RC=$?" >> out`), not a
pipeline tail. An earlier reading of `rc=0` was an artifact of reading `$?` after
a pipe — the shell reported the tail of the pipeline, not lint. **No change to
the exit-code logic is warranted.** The residual weakness is discoverability
only: in a run spanning thousands of files the PARSE001 line scrolls past, and
the trailing summary (`NOT LINTED: N file(s) could not be parsed and were never
analysed`) is easy to miss. Treat that summary line as the thing to grep.

## Census

Method (the per-invocation startup tax is ~4.4s regardless of target, so
per-file invocation is unusable at tree scale):

```sh
# directory argument = ONE startup amortised across the whole subtree
for d in src/compiler src/lib src/app src/runtime src/i18n src/os; do
  ( timeout 5400 bin/simple lint $d/ > cen_$(echo $d|tr / _).txt 2>&1
    echo "SENTINEL_DONE_RC=$?" >> cen_$(echo $d|tr / _).txt ) &
done; wait
```

**Arm a completion sentinel; never conclude from an absence.** A polling
`grep` over a still-running (or killed) log reports "no parse errors" simply
because the file has not been linted yet. During this very census an earlier
whole-`src/` run was killed mid-flight and its log showed **zero** PARSE001
hits with `SENTINEL_EXIT=143` — a false clean that would have closed the task
wrongly. Check the sentinel line before reading the result.

### Results — 2 files, both fixed

| file | parser message | category | disposition |
|------|----------------|----------|-------------|
| `src/compiler/55.borrow/gc_analysis/mod.spl:246` | unexpected token in expression: Dedent | (e) empty `case` body | fixed, `5b453f84f40` |
| `src/runtime/hooks.spl:149` | expected parameter name | trailing comma in method params | fixed, `fd164851615` |

Two further empty-`case` sites were found by a text prefilter (below) rather
than by lint, because their files parsed anyway:

| file | category | disposition |
|------|----------|-------------|
| `src/app/examples_check/main.spl:350` | (e) empty `case` + **behavioural miscount** | fixed, `5b453f84f40` |
| `src/compiler/35.semantics/macro_check/template.spl:310` | (e) empty `case` body | fixed, `5b453f84f40` |

No intentionally-uncompiled fixtures appeared in the census.

## Cause 1 — empty `case` arms (refactor damage, shape (e))

The `impl X:` → free-function refactor left `case` arms with a header and no
body. Correct bodies were determined from sibling arms, not guessed:

- `gc_analysis/mod.spl` and `template.spl` → `pass_do_nothing`. Both matches
  dispatch purely for side effects and their sibling default arms are no-ops
  (`process_terminator` already has `case _: pass`); `template.spl` falls
  through to its `"tt"  # Default to token tree` tail expression.
  `pass_do_nothing` is a first-class no-op keyword (see
  `src/compiler_rust/compiler/src/hir/lower/module_lowering/function.rs`), used
  694x in `src/`, not a placeholder.
- `examples_check/main.spl` was **not** merely cosmetic. The line following the
  empty `case _:` sat at the *match's* indentation rather than the arm's:

  ```spl
  case "CRASH":
      stats.crashed = stats.crashed + 1
  case _:
  stats.failed = stats.failed + 1     # ran for EVERY result, incl. PASS
  ```

  so `stats.failed` was incremented unconditionally. The three sibling arms each
  increment exactly one counter, which fixes the intended reading.

### Text prefilter (finds shape (e) even where the file still parses)

Walk `src/**/*.spl`, skip comments and triple-quoted blocks, and flag any line
matching `^(case .*|else|_):\s*(#.*)?$` whose next non-blank, non-comment line
is indented **≤** the case header. Tree-wide this yields 5 hits: the 3 real ones
above plus 2 false positives (`module_loader.spl` `case _("…")` arms that do
have bodies, and a `html_render.spl` line whose CSS braces in a text literal
parse as interpolation). A naive `case.*:$` grep returns ~8,200 hits and is
useless.

## Cause 2 — pure-Simple parser rejects a trailing comma in class-method params

`src/runtime/hooks.spl` is **not** refactor damage. The Rust seed compiles it
fine — `simple run` parses it without complaint — so only lint, which uses the
pure-Simple parser, ever saw a problem. That seed-vs-pure-Simple divergence is
why it survived: nothing that compiles the file could observe it.

Minimal repro (top-level `fn` is unaffected; the trigger is a method in a class):

```spl
class C:
    n: i64
    me m(
        a: text,
    ) -> i64:
        self.n
```

`parse_class_body_method` (`src/compiler/10.frontend/core/parser_decls_use.spl`,
loop at ~558) consumed the comma and then called `parser_expect_param_name()`
unconditionally; on a trailing comma the next token is `)`. The **three sibling
param loops all guard exactly this** — `parser_decls_fn.spl:210` and
`fn_struct_decls.spl:598`/`:683` each break on `TOK_RPAREN` after the comma — so
this copy was simply missing the guard and the fix restores it.

Impact: `hooks.spl` is 526 lines and was receiving zero AST lints.

### Family scope — 6 sites, all fixed by the one parser change

A structural sweep (multi-line `me`/`fn`/`static fn` param list inside a
`class`/`struct`/`enum` whose last param line ends in `,`) finds every site the
defect could reach:

```
src/runtime/hooks.spl:143                                  me add_breakpoint_with_options(
src/app/dap/hooks.spl:143                                  me add_breakpoint_with_options(
src/lib/dap/hooks.spl:143            (nogc_sync_mut)       me add_breakpoint_with_options(
src/lib/dap/hooks.spl:143            (nogc_async_mut)      me add_breakpoint_with_options(
src/lib/gc_async_mut/gpu/session/backend_adapter_shared.spl:73   static fn create(
src/os/drivers/dma/dma_descriptor.spl:50                        static fn create(
```

All six are repaired by the single guard in `parse_class_body_method` — no
source edits were needed at the call sites, which is the correct fix direction:
the syntax is legal and the parser was wrong. Note only `src/runtime/hooks.spl`
surfaced in the lint census; the other five sit in subtrees whose lanes had not
reached them, which is precisely why the sweep was run *in addition to* the
census rather than instead of it.

## Verification

Parse fixes: PARSE001 gone **and** rc back to 0.

Parser fix, RED→GREEN→SABOTAGE on the interpreter path (`.spl` edits are live,
no rebuild): RED = repro gives PARSE001 at 5:5, rc=1. GREEN = "Lint passed: all
files clean", rc=0, and `hooks.spl` clean. SABOTAGE = deleting just the two
added guard lines restores PARSE001 at 5:5 and rc=1, proving the probe is real.

`gc_analysis` behaviour, RED/GREEN/SABOTAGE via a probe calling
`register_gc_type`/`is_gc_type`: reports `before42=false after42=true
other7=false`; neutering the `.push` gives `after42=false`.

## Correction to an earlier claim in this session

Commit `5b453f84f40`'s message asserts that commit `0f0a3270192`'s
`gc_types.contains/.push` fix "stayed dead until this commit" because the file
never parsed. **That is wrong**, and it is recorded here rather than left
standing:

- Probing the **pre-fix** blob directly gives `before42=false after42=true` —
  the symbols already worked.
- The AST-lint warning set for `gc_analysis/mod.spl` is byte-identical either
  side of the parse fix (same 6 warnings at 111/112/184/195/211/226), so those
  lints were already running.

The Rust seed tolerates the empty `case _:` that the pure-Simple parser rejects.
Only the pure-Simple lint path was blind, and only for the AST lints it had
already produced. The parse fixes remain correct and worth having — the
`examples_check` miscount was a genuine behavioural bug — but "a landed fix was
inert" does not hold. (Separately: `gc_analysis` has **zero importers**
tree-wide, so nothing else consumed it either.)

## Follow-ups

- `gc_analysis/` has no importers anywhere in `src/`. Either wire it up or
  delete it; it is currently dead weight carrying real logic.
- Consider auditing for other pure-Simple-parser-only rejections: any construct
  the seed accepts but the pure-Simple parser does not silently disables lint
  for that whole file. The trailing-comma case was found only because a census
  was run; there is no standing gate for this class.

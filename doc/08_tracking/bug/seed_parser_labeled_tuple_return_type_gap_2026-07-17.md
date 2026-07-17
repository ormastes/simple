# Parser cannot parse labeled-tuple return types (`-> (name: type, ...)`) — Stage-1 bootstrap blocker

**Date:** 2026-07-17
**Scope:** shared `.spl` frontend parser (`src/compiler/10.frontend/core/...`),
used by both the frozen Rust seed (`src/compiler_rust/target/bootstrap/simple`)
and the current self-hosted binary (`bin/simple`).
**Severity:** high — was blocking Stage-1 bootstrap end-to-end (see repro below).
**Status:** worked around at the one bootstrap-critical call site (see Fix);
the underlying parser gap is NOT fixed.

## Symptom

`-> (name: type, name: type, ...)` — a **documented** function return-type
form (`doc/07_guide/quick_reference/syntax_quick_reference.md`, "Multi-Return
Tuples" section, the `div_rem` example) — fails to parse in both the frozen
Stage-1 seed and the current self-hosted `bin/simple`:

```
$ src/compiler_rust/target/bootstrap/simple check probe.spl
[parser_error] path probe.spl line 1:34: expected ), got : ':'
[parser_error] line 1:39: unexpected token in expression: , ','
...
```

Minimal probe (also fails identically against `bin/simple check`):

```simple
fn div_rem(n: i64, d: i64) -> (quotient: i64, remainder: i64):
    return (quotient: n / d, remainder: n % d)

fn main():
    val r = div_rem(10, 3)
    print r.quotient
```

This is the exact example from the syntax quick reference — not a
codebase-specific construct. It also reproduces on every pre-existing
labeled-tuple-return function already in the tree (none of these are new):
`src/lib/nogc_sync_mut/tooling/regex_utils.spl:192`,
`src/lib/nogc_sync_mut/tooling/regex_match.spl:50`,
`src/lib/common/image/image_info.spl:259,310`,
`src/lib/nogc_sync_mut/game_net/txn.spl:46`,
`src/app/office/file_formats.spl:49,169,186`, others (`grep -rn -- "-> (\w\+: "`).
These never surfaced as a build break because none of them sit on
`bootstrap_main.spl`'s entry-closure import graph with the pipeline's
hard-abort-on-first-parse-error policy (see "How this blocked Stage-1"
below) — they are presumably broken too, just unexercised on that path.

## How this blocked Stage-1

`src/lib/nogc_sync_mut/io_runtime.spl:173` (`process_run`) was changed by
commit `50c3393119e` (today) from an unlabeled tuple return
(`-> (text, text, i64)`) to a labeled one
(`-> (stdout: text, stderr: text, exit_code: i64)`) to fix a *different*,
narrower bug: an unlabeled tuple with two repeated `text` fields trips a
standalone-compile-mode-only "anonymous multi-return tuple contains repeated
field types" ambiguity check the moment an entry file does `.0`/`.2` access
or destructuring on the result (see
`doc/08_tracking/bug/mcp_main_lazy_json_standalone_compile_process_run_tuple_ambiguity_2026-07-17.md`).

`io_runtime.spl` is imported (transitively) by `src/app/cli/bootstrap_main.spl`,
so it is always in scope for:

```
src/compiler_rust/target/bootstrap/simple native-build --source src/app \
  --entry-closure --strip --threads 1 --timeout 420 \
  --entry src/app/cli/bootstrap_main.spl -o <out> --backend=llvm-lib
```

Under `--entry-closure`, `driver.spl`'s `parse_all_impl` (phase 2) parses
every reachable source and hard-aborts the whole build on the *first* file
with a parse error (`self.ctx.errors.push("parse error in {path} ..."); return false`)
— it does not skip/continue past a broken module. With `process_run`'s
labeled-tuple signature unparseable, phase 2 failed immediately, `ctx.errors`
was non-empty, but that specific error text was not what ultimately reached
the CLI (`[STDERR] error: native-build failed without diagnostics` in one
run; a downstream `total_modules <= 0` guard —
`src/compiler/80.driver/driver_aot_output.spl:304-309`,
`"produced empty mir_modules ... no modules loaded"` — is the other observed
manifestation, both stemming from the same "no modules survived phase 2"
condition). Either message is a *symptom*; the parse error is upstream and
was the true blocker.

## Fix applied (root cause is small; parser fix is not)

Reverted `process_run`'s signature in `src/lib/nogc_sync_mut/io_runtime.spl`
to the pre-`50c3393119e` unlabeled tuple (`-> (text, text, i64)`), since:
- the labeled form the codebase and docs sanction cannot be parsed by the
  frozen Stage-1 seed at all (not a small fix — this is a shared-parser
  grammar gap, out of scope for a root-cause source edit);
- `io_runtime.spl` sits on the bootstrap-critical entry-closure path, so any
  parse failure here is a hard Stage-1 blocker, unlike the other ~14
  pre-existing (and presumably also-broken) labeled-tuple-return files
  elsewhere in the tree;
- the standalone-compile "repeated field types" ambiguity this reintroduces
  is narrow (only entry files doing `.0`/`.2`/destructuring access on
  `process_run`'s result during standalone compile, e.g.
  `src/app/mcp/main_lazy_json.spl`) and should be fixed at that call site,
  not by breaking parsing for all ~150 `process_run` callers plus the whole
  Stage-1 bootstrap.

Function body is unchanged (`rt_process_run(cmd, args)`).

**Rerun confirmation:** re-ran the exact Stage-1 repro
(`native-build --source src/app --entry-closure --strip --threads 1
--timeout 420 --entry src/app/cli/bootstrap_main.spl --backend=llvm-lib`)
after the revert. Zero `[parser_error]` / "phase 2 FAILED" / "empty
mir_modules" output this time — phase 2 now parses cleanly and the build
proceeds through the full compiler+LLVM import graph into codegen. It then
hit a *different*, expected resource limit: `[TIMEOUT: Process killed after
420s]` / "native-build worker timed out after 420s before producing a
binary" (single-threaded interpreted worker loading the whole compiler +
LLVM closure before any codegen exceeds the 420s/`--threads 1` budget for
this large a `--source` tree) — the tool's own error message suggests
raising `--timeout`, shrinking `--source`, or using the in-process backend.
That is a separate, pre-existing scaling characteristic, not a new bug, and
is out of scope for this parse-blocker fix.

## Still open

1. **Parser gap** (this doc): `-> (name: type, ...)` labeled-tuple return
   types don't parse in either the frozen seed or the current self-hosted
   binary, despite being documented language syntax. Needs a fix in the
   shared `.spl` frontend parser (`src/compiler/10.frontend/core/...`,
   function-signature / type parsing), followed by seed rebuild+redeploy for
   Stage-1 to ever consume it.
2. `main_lazy_json.spl`'s standalone-compile ambiguity
   (`mcp_main_lazy_json_standalone_compile_process_run_tuple_ambiguity_2026-07-17.md`)
   is reopened by this revert and needs a call-site-local fix (not a
   `process_run` signature change).

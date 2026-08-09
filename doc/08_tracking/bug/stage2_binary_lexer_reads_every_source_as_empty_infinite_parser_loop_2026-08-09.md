# Stage-2 binary lexes EVERY source file as empty → unbounded parser-error loop

Date: 2026-08-09
Status: **OPEN — reproduced, root symptom isolated, not fixed**
Area: bootstrap / stage-2 native-build / 10.frontend lexer / parser error recovery

## Summary

A full `--full-bootstrap` from a clean pinned `origin/main`
(`f026cfcf510d12758048c1bad585ccd59d9764fa`) produced a Stage-2 binary that
reports **806 compiled, 0 failed**, links a 126 MB executable, and **passes the
"Stage 2: running bootstrap compiler sanity" gate** — yet that binary **cannot
lex a single source file**. Every file, including a hand-written two-line one,
is read as an empty token stream, and the parser's error recovery then loops
**forever** without advancing.

This is a **silently vacuous Stage 2**: the build is green on every signal the
wrapper checks, and the artifact is non-functional.

## Reproduction (exact)

```
SIMPLE_MIR_STMT_CALLER_DEBUG=1 SIMPLE_MIR_GARBAGE_EXPR_DEBUG=1 \
  sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy \
  --output=/home/ormastes/dev/simple-build-out/stage3-nilrecv-20260809-v3 --progress
```

Checkout: `/home/ormastes/dev/simple-s3verify-20260809`, pinned to
`f026cfcf510`, `git status` clean apart from pre-existing CRLF noise in 10
`.cmd`/`.bat` files. Host at launch: load 8.2, 1.4 T free on `/`, 108 G RAM
available.

## Evidence

### 1. Stage 2 reports complete success

`logs/x86_64-unknown-linux-gnu/stage2-native-build.log` in full (358 bytes):

```
Linked: .../stage2/x86_64-unknown-linux-gnu/simple (126193 KB) via clang++
Build complete: 806 compiled, 0 cached, 0 failed
  Binary: .../stage2/x86_64-unknown-linux-gnu/simple (126193 KB)
  Time: 125.9s compile + 68.5s link = 194.3s total
```

The wrapper then printed `Stage 2: running bootstrap compiler sanity` and
admitted the binary to Stage 3.

### 2. The binary runs, but its lexer is dead

The binary itself is alive and is not size-vacuous (129,222,000 bytes):

```
$ .../stage2/x86_64-unknown-linux-gnu/simple --version
simple-bootstrap 1.0.0-beta          # rc=0
```

But `native-build` on a **two-line file written by hand** fails identically to
the real entry point:

```
$ printf 'fn main():\n    print("hi")\n' > probe_tiny.spl
$ .../stage2-admitted/simple native-build --target x86_64-unknown-linux-gnu \
    --backend llvm -o /tmp/s3probe/tiny probe_tiny.spl
[parser_error] line 1:1: unexpected token in expression: Unknown(0) ''
[parser_error_ctx] path probe_tiny.spl kind 0 text ''
[parser_error] line 1:1: unexpected token in expression: Unknown(0) ''
[parser_error_ctx] path probe_tiny.spl kind 0 text ''
... forever
```

`text ''` and `Unknown(0)` at `line 1:1` mean the lexer handed the parser an
**empty/unknown token for a non-empty file**. This is not entry-file specific
and not source specific — it is every file.

### 3. The parser error-recovery loop is unbounded

Stage 3 ran 11 minutes and produced:

- `stage3-native-build.log` = **444,103,752 bytes / 6,299,344 lines**
- `sort -u` over the **entire** log = **2 distinct lines** (the pair above)
- process at **100% CPU** (TIME 11:09 / ELAPSED 11:13) and **32.4 GB RSS**, still climbing

So the failure is not merely a bad diagnosis — error recovery makes **no
forward progress**, and both the log and RSS grow without bound. Left alone
this fills the disk or OOMs the host. (This is the same hazard class that wiped
`main` twice via ENOSPC on 2026-08-01; the run was killed deliberately.)

### 4. It is NOT a checkout artifact — ruled out explicitly

- entry file on disk: `src/app/cli/bootstrap_main.spl`, **21,918 bytes**, real
  content (`extern fn sys_get_args() -> [text]` …), `git diff HEAD` on it is
  **empty** — byte-identical to the pinned blob.
- the failing process's `cwd` is `/home/ormastes/dev/simple-s3verify-20260809`
  (read from `/proc/639991/cwd`), and the entry file **is** visible and readable
  at exactly the relative path passed on the command line.
- the **Rust seed** read those same 806 files fine while building Stage 2. Only
  the produced pure-Simple binary cannot read them.

## Where to look

The lexer/tokenizer used by the pure-Simple `native-build` path returns an empty
token stream for a file whose bytes are present. Two independent defects are
stacked here and BOTH deserve fixing:

1. **The lexer returns empty for a non-empty file** (the root cause).
2. **The parser's error recovery does not guarantee forward progress** — on an
   unconsumable token it re-reports at the same position forever instead of
   advancing or aborting. Even after (1) is fixed, (2) will turn any future
   lexer defect into an unbounded disk/OOM event rather than a diagnosis. A
   bounded error count / mandatory-advance invariant belongs in the parser loop.

## Gate defect (file/fix separately if not already tracked)

**`Stage 2: running bootstrap compiler sanity` is fail-open.** It admitted a
compiler that cannot parse a two-line file. A sanity gate that a
totally-non-functional binary passes provides no signal. Minimum bar: compile a
trivial fixture end-to-end and assert a non-vacuous artifact plus a bounded
runtime — the exact probe used in Evidence §2 would have caught this in seconds.

## Consequence for the nil-receiver SIGILL bug

This is **blocker 12** in front of
`stage3_selfhost_nil_receiver_sigill_in_lower_expr_caller_2026-08-05.md`. Stage 3
never reached HIR or MIR lowering — it never got past lexing its entry file — so
the SIGILL fault site **still has never executed**. Measured over the full
444 MB Stage-3 log: `field access on nil receiver` = 0, `SIGILL`/exit 132 = 0,
`[mir-stmt-caller]` = 0, `garbage-expr` = 0. Both probes were enabled and both
produced nothing.

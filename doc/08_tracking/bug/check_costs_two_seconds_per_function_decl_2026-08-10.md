# `simple check` costs ~2s per function declaration (parse), plus ~20s fixed per worker

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Found:** 2026-08-10, stream K3, following stream G3 (`a39229b1eb0`)
- **Severity:** blocks directory-wide parse gating; `simple check src/app` is tens of hours

## Symptom

`simple check <file>` takes 20-110s for a *tiny* file. `simple check <dir>`
spawns one worker per file (`src/app/cli/check_entry.spl`), so 2,544 files in
`src/app` is tens of hours. A DAP spec that shelled out to `check` looked like
an infinite hang.

## Binary identity for every number below

    bin/simple -> bin/release/x86_64-unknown-linux-gnu/simple
    29,577,536 bytes, mtime 2026-08-09 04:50:31 UTC

This binary is itself the **Rust bootstrap seed** — it prints
"this Rust-built Simple binary is a bootstrap seed only" on every run.
`bin/simple_seed` is a **dangling symlink**
(`-> release/x86_64-unknown-linux-gnu/simple_seed`, target absent), so the
delegation rationale in the `check_entry.spl:14-19` comment does not apply on
this machine: nothing delegates, the seed runs the worker itself.

## Profile — where the time actually goes

Measured externally with the shell, `SIMPLE_TIMEOUT_SECONDS=3600`, on a box at
**load average 79-117** (six other agent streams). All numbers therefore
*overstate* absolute cost; the ratios are the finding.

| measurement | wall | note |
|---|---|---|
| `run hello.spl` (no imports) | **0.078s** | interpreter startup is not the problem |
| `run` a file whose only `use` is `compiler.core.parser` | 13.7s / 25.9s | two runs, load 103 / 91 |
| `use compiler.core.ast` alone | 4.53s | |
| `use compiler.frontend.core.lexer` alone | 6.52s | |
| `compiler.core.types`, `file_discovery`, `app.check.*` | 0.42-1.71s each | negligible |
| `check` a **1-function** file | 17.7s wall | `--phase-profile`: in-main **2.49s**, of which parse **2.317s** |
| `check` a **41-function** file (1.4 KB) | 109.2s wall | in-main **83.98s**, of which parse **83.773s** |

Everything outside parse is noise: `scope_setup` 61ms, `source_read` 0ms,
`lint` 95ms, `scope_teardown` 42ms.

## Cost shape

Two independent terms:

1. **Fixed pre-main cost, ~15-25s per worker process** — the seed re-reads and
   re-interprets `src/app/check/main.spl` and its import closure from source
   every invocation. `compiler.core.parser` is essentially all of it.
   (17.7s wall - 2.49s in-main = 15.2s; 109.2 - 84.0 = 25.2s.)
2. **Parse cost, ~2.0s per function declaration of the *target* file** —
   1 fn -> 2.317s, 41 fn -> 83.773s. That is **2.32 vs 2.04 s/fn**, i.e.
   linear at ~2s/decl with a negligible constant, over this range.

Cost is **not** per-file-constant, **not** per-byte, and (over 1..41 decls) not
detectably superlinear. It is per function declaration. This is the same
magnitude the lint startup-tax note records for `bin/simple lint`
(~3.3-4.0s per function decl) — `check` and `lint` share the self-hosted
parser, and this is one defect, not two.

Practical consequence: a real source file with 30 decls costs ~20s + 60s = 80s.
2,544 files is ~56 hours, and **batching cannot fix more than ~25% of it**.

## Root cause

`parse_module` — the self-hosted Simple parser — is being **tree-walk
interpreted** by the seed, once per target file. The seed's own native Rust
parser handles these files in milliseconds; running the Simple parser under the
seed's interpreter is roughly three orders of magnitude slower per declaration.

## What would fix it, with payoff

1. **(Real fix, architectural)** `check` must not interpret the self-hosted
   parser. Either make `check` a compiled subcommand of the deployed pure-Simple
   binary — `cli_check()` already exists at
   `src/app/io/_CliCommands/handler_commands.spl:239` — or AOT-compile
   `src/app/check/main.spl` once into a native worker binary and spawn that.
   Payoff: removes **both** terms. Expected ms/file; `src/app` goes from tens of
   hours to seconds-to-minutes. This is the only fix worth doing.
2. **(Mitigation, landed)** Chunk the per-file worker spawn 32 files at a time
   in `check_entry.spl`, re-running a failing chunk file-by-file to preserve
   per-file attribution and crash isolation. Removes term (1) only: ~20s saved
   per file. Measured on 8 mixed files (58 decls total): **153.0s in one worker
   vs ~276s** for the same 8 as separate spawns (8 x 20s pre-main + 116s parse)
   — a ~45% saving. Does not make directory-wide gating feasible on its own.

## Why there is no `check` cache equivalent to `scripts/check/lint-cached.shs`

A content-hash cache of CLEAN verdicts would work here exactly as it does for
lint, and would make *re-*checking an unchanged tree free. It does not help the
first pass, and the first pass is the ~56-hour number. Fix (1) first; a cache on
top of a millisecond-per-file checker is not worth the invalidation surface.

## Reproduce

    export SIMPLE_TIMEOUT_SECONDS=3600
    B=bin/release/x86_64-unknown-linux-gnu/simple
    # 41 trivial functions
    python3 -c 'print("".join(f"fn f{i}(a: i64) -> i64:\n    a + {i}\n\n" for i in range(40)) + "fn main() -> i64:\n    0\n")' > /tmp/f40.spl
    time $B run src/app/check/main.spl /tmp/f40.spl --phase-profile

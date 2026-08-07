# `run` missing from staged bootstrap binaries — NOT A DEFECT (closed)

Date: 2026-08-07
Status: CLOSED — not a defect; no code change made
Area: bootstrap / CLI surface

## Claim under investigation

`src/app/cli/bootstrap_main.spl` does not wire a `run` subcommand, so "19
callers are structurally red" — every script that shells out to
`simple run <file>` against a staged/bootstrap binary cannot work.

## Verdict

The premise is false. `run` is absent from `bootstrap_main.spl` **by design**,
and **zero** callers target a staged binary. Nothing is red. No fix was made,
because there is nothing to fix.

## Evidence

### 1. `run` is present in the production CLI

`bootstrap_main.spl` is not the product CLI. It is a deliberately minimal
bootstrap driver whose entire command surface is `compile` and `native-build`.
The full CLI lives at `src/app/cli/main.spl` with `src/app/cli/dispatch.spl`,
and its dispatch table declares `run` at `src/app/cli/dispatch/table.spl:520`.

### 2. Positive invocation, not a grep

Reading help text is not proof, so each binary was actually made to execute a
trivial program (`fn main` printing a sentinel):

| binary | result |
|---|---|
| `bootstrap/stage2/simple run probe.spl` | `error: unknown command 'run'` |
| `bootstrap/stage3/simple run probe.spl` | `error: unknown command 'run'` |
| `bin/simple run probe.spl` | printed `RUNPROBE_OK` |

Engine note: `bin/simple` announces `this Rust-built Simple binary is a
bootstrap seed only`. So the passing row is **seed** coverage. There is still no
deployed pure-Simple binary (stage 3 blocked on an unrelated inline-asm bug), so
no self-hosted claim is made here either way.

### 3. No caller targets a staged binary

All `simple ... run` call sites under `scripts/**/*.shs` were enumerated and
grouped by how each resolves its binary:

| resolution | count |
|---|---|
| `bin/simple` (incl. `$ROOT_DIR/`, `$repo_root/` prefixed) | 25 |
| `bin/release/x86_64-unknown-linux-gnu/simple` | 2 |
| `"$simple_bin"` (assigned to `bin/simple`) | 2 |
| `./src/compiler_rust/target/debug/simple` (Rust seed) | 1 |
| **`bootstrap/stage*/simple`** | **0** |

30 call sites, not 19. Every one resolves to the production CLI path or the
Rust seed — both of which carry `run`. The staged artifacts are never asked
for it.

### 4. `run` was never removed

`git log -- src/app/cli/bootstrap_main.spl` on origin/main shows two commits
(`069cbce8090`, `cfe0506e336`); neither touches the dispatch region. There is no
commit that deleted a `run` arm, so there is no removal rationale to recover.

## Why wiring `run` here would be actively wrong

`bootstrap_main.spl` exists to keep the stage2/stage3 self-compilation surface
small. `run` requires the interpreter/JIT execution path, which would pull that
whole subsystem into the stage entry point — the opposite of the file's purpose.

It would also walk into a known hazard: `native-build --entry X` is on record as
delegating to the Rust runtime, and stage 3 once silently stopped self-hosting
through `--entry`. A `run` added here would most likely execute via the seed
while appearing to be staged output, which is precisely the failure mode that
`reference_simple_test_silently_delegates_to_seed_child` describes.

## What the original report was probably remembering

`doc/08_tracking/bug/bin_simple_bootstrap_main_stage_deployed_no_subcommands_2026-08-01.md`
records a real incident with the same surface symptom: a **stage artifact was
deployed over the production `bin/simple` path**, so `bin/simple run` answered
`error: unknown command 'run'`. That was a deploy defect, it was fixed by
redeploying the canonical driver, and it is already closed. The lesson there is
"do not deploy a stage artifact to the production path" — not "add `run` to the
stage artifact".

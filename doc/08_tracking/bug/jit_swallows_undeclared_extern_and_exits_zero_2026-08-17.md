# JIT logs an undeclared extern, then continues and exits 0 with a wrong value

**Status:** OPEN (P1)
**Filed:** 2026-08-17
**Component:** JIT extern resolution
**Class:** silent wrong result — engine divergence on an error path

## Symptom

Call an extern that is not declared anywhere (measured with `rt_sha256_hex`):

| `SIMPLE_EXECUTION_MODE` | rc | behaviour |
|---|---|---|
| `interpret` | 1 | fails correctly — the missing extern is an error |
| `jit` (and unset, which JITs) | **0** | logs the error, **continues**, and returns a wrong value (`len=-1`) |

The interpreter treats an unresolvable extern as fatal. The JIT reports it and
carries on, so the program exits successfully with a fabricated result.

## Why this is worse than a crash

This is the campaign's target class exactly: compiles clean, exits 0, hands back
a wrong answer. A caller sees `len=-1` and no failure signal. Worse, it is
*mode-dependent* — the same source is correct under the interpreter and wrong
under the JIT, which is the default engine, so a spec body (which runs
interpreted) can never observe it.

It is also a fail-open on the exact axis that hid a missing P-256 implementation
behind a public API earlier in this campaign: an unresolved symbol that only
warns.

## Reproduction

Call any undeclared `rt_*` function and compare the two pinned arms:

```
SIMPLE_EXECUTION_MODE=interpret bin/simple run <probe>   # rc=1, correct
SIMPLE_EXECUTION_MODE=jit       bin/simple run <probe>   # rc=0, len=-1
```

Read rc into a variable on the line AFTER the command — never through a pipe.

## Fix direction

The JIT's unresolved-extern path should be fatal by default, matching the
interpreter. If a permissive mode is genuinely wanted for partial builds, it
belongs behind an explicit opt-in flag and must still refuse to return a
fabricated value.

Related, already in the tree: `SIMPLE_JIT_STRICT=1` turns some JIT fallbacks into
hard errors (`jit.rs:157`). Whether it covers this path was not tested.

## Not verified

- Whether the native/AOT lane shares the behaviour (untested — a third engine).
- Whether `SIMPLE_JIT_STRICT=1` already makes this fatal.
- Whether the same swallow applies to a *declared* extern whose symbol is missing
  at link time, as opposed to an undeclared one.

Found incidentally while working the os/runtime slice; the reporting lane's scope
did not cover the JIT, so it is filed rather than patched.

## Triage 2026-09-13 (BUGFIX-7 lane)

Reproduced on `a6450c9d6f5` with `rt_totally_undeclared_symbol_zzz` (Rust
seed, `bin/release/aarch64-unknown-linux-gnu/simple`):

```
SIMPLE_EXECUTION_MODE=interpret bin/simple run probe.spl   -> rc=1, correct
SIMPLE_EXECUTION_MODE=jit       bin/simple run probe.spl   -> rc=0, len=0
```

matching the documented shape (this repo's build reports `len=0`, not
`len=-1` — a detail difference, same defect class: a wrong value with rc=0).

Answered two of the three "Not verified" questions:

- **`SIMPLE_JIT_STRICT=1` is not the relevant knob** (or does not exist under
  that name in this build) — testing it changed nothing.
- **The real opt-in is `SIMPLE_STRICT_EXTERN=1`**, and it DOES make this fatal:
  `SIMPLE_EXECUTION_MODE=jit SIMPLE_STRICT_EXTERN=1 bin/simple run probe.spl`
  -> `rc=1`, `error: extern 'rt_...' (argc=1) is declared in Simple but backed
  by no implementation; SIMPLE_STRICT_EXTERN=1 refuses to substitute nil for
  it.` So the safety mechanism already exists; it is merely not the default,
  which is exactly the record's own fix direction ("belongs behind an
  explicit opt-in flag" — it already is one, but the ask was arguably for
  fatal-by-default).

Not fixed here: the actual behavior (interpreter_sffi.rs / JIT extern
resolution path) is Rust seed source, and making a mode's *default* stricter
requires a rebuild+redeploy to verify — out of scope for this lane. Third
question (declared-but-missing-at-link-time extern) not tested; out of budget.
Left OPEN.

# `Type.method(arg)` static-call form: claimed silent-nothing NOT reproduced — already errors correctly (VERIFIED, closed as false positive)

## Claim under investigation

Reported 2026-08-11 while authoring an unrelated capability gate: `print
f64.sin(0.0)` (TYPE-qualified call-form, as opposed to the method form
`(0.0).sin()`) produced NO output and NO error — silent nothing. A separate
probe reportedly saw `variable f64 not found` for bare `f64.sin(0.0)` in
expression position.

## Verification method

Fresh seed build from a clean checkout, not the possibly-stale deployed
`bin/simple` (this worktree at `/mnt/data/dev/pub/simple` has no `bin/simple`
at all — see `reference_worktree_isolation_has_no_bin_simple_binary.md`):

```
cd src/compiler_rust
CARGO_TARGET_DIR=/mnt/data/cargo-target-sinform cargo build --release -p simple-driver --bin simple
```

Binary: `/mnt/data/cargo-target-sinform/release/simple`, 58725480 bytes,
mtime `2026-08-11 04:45:08`.

All probes wrap the expression in `fn main():` (top-level bypasses the JIT
per project rules) and compare **stdout/stderr content**, never just exit
codes, across both the interpreter/JIT-fallback lane (`simple <file>` /
`simple run <file>`) and the native lane (`simple compile <file> --native -o
<out> && ./<out>`).

## Truth table (fresh build, both lanes)

| Expression | Position | Interp lane | Native lane |
|---|---|---|---|
| `f64.sin(0.0)` | `print` arg | `error: semantic: variable \`f64\` not found` (via `run`) / `error: semantic: Undefined("undefined identifier: f64")` (via `compile`), exit 1 | same `Undefined("undefined identifier: f64")`, compile exit 1 |
| `f64.sin(0.0)` | bare statement | same error, exit 1 | same error, compile exit 1 |
| `val x = f64.sin(0.0); print x` | typed local | same error, exit 1 | same error, compile exit 1 |
| `i64.abs(-3)` | `print` arg | `variable \`i64\` not found` / `Undefined("undefined identifier: i64")`, exit 1 | same, compile exit 1 |
| `f64.sqrt(16.0)` | `print` arg | `variable \`f64\` not found` / `Undefined("undefined identifier: f64")`, exit 1 | same, compile exit 1 |
| `1 + 1` (negative control) | `print` arg | prints `2`, exit 0 | n/a (interp-only control) |

**No silent-nothing was observed in any of the 5 forms x 2 lanes = 10 probes.**
Every probe produced a proper semantic error with non-empty stderr text and a
non-zero exit code, in both the `run`/JIT-fallback path and the standalone
`--native` compiled-binary path. The one wrinkle: via `simple run <file>`
(the JIT-fallback path) there is a `[jit-fallback] unresolved external symbol
'f64_dot_sin'` warning line printed to stdout/stderr *before* the semantic
error is raised (the JIT attempts and fails first, then falls back to the
interpreter which raises the real semantic error) — this is noisy but not
silent, and the process still exits non-zero with the real error as the last
line.

The originally reported "no output and no error" was not reproduced on a
fresh build in either lane. Given the project's standing note that several
claimed defects that day were false, and given this repo's `bin/simple`
symlink is known to go stale/diverge from source
(`reference_bin_simple_symlink_stale_scratch_build_and_verify_binary_provenance.md`),
the most likely explanation is a stale or otherwise non-representative
deployed binary was used for the original observation, not a defect in
current source.

## Ruling: current behavior (hard semantic error, both lanes) is CORRECT — no code fix required

Basis, from repo evidence:

- `grep -rn` across `src/lib/**` and `test/**` for genuine `f64.method(...)` /
  `i64.method(...)` **static-call** usage (receiver is the bare type name,
  not a variable) turns up **zero** real call sites. The one incidental hit
  (`test/01_unit/lib/hardware/vhdl_gen/probe_exec_core_gen.spl:47`,
  `f64.len()`) is a local variable named `f64`, not the type — confirming the
  language has no static `Type.method(args)` call convention anywhere in the
  codebase.
- The only supported numeric-math call form is the **method/receiver** form,
  `(0.0).sin()`, `x.sqrt()`, `x.abs()` — see
  `src/compiler_rust/compiler/src/hir/lower/expr/mod.rs:958-1039` (float/int
  math method dispatch) and the two related, already-tracked bug docs
  `doc/08_tracking/bug/float_and_int_math_methods_missing_on_numeric_receivers_2026-08-10.md`
  and
  `doc/08_tracking/bug/float_literal_receiver_method_call_returns_receiver_2026-08-10.md`.
- Since `f64`/`i64` are type names, not bindable identifiers, `f64.sin(0.0)`
  parses as ordinary field/method-call postfix on an identifier expression
  `f64` — and correctly fails semantic analysis with "undefined identifier:
  f64" because no such variable exists. This is the same, consistent
  "unresolved identifier" error path used for any other undefined-variable
  reference in the language; there is no separate carve-out that would make
  this case special.

**Ruling: (b) — silent-nothing being the only unacceptable outcome, and
silent-nothing is not what happens.** The existing behavior (proper
parse/semantic error, non-zero exit, identical diagnostic text in both
lanes) already satisfies the stated acceptance bar. No source change is
required or made by this doc.

## Root cause of the *original mis-report* (best-effort, not fully provable)

Not conclusively determined — no stale `bin/simple` was available in this
worktree to diff against (`reference_worktree_isolation_has_no_bin_simple_binary.md`).
Filed as a verification/measurement note rather than a code defect. If a
future session reproduces true silent-nothing output, re-open with the exact
binary path + `stat` mtime + `--version`/provenance probe output, per
`reference_bin_simple_symlink_stale_scratch_build_and_verify_binary_provenance.md`.

## Red-then-green check script

`scripts/check/check-type-qualified-static-call-error.shs <path-to-simple-binary>`

Verdict convention (last stdout line):
- `PASS — <n> check(s), 0 failures` (exit 0)
- `FAIL — <n> of <m> check(s) failed: <names>` (exit 1)
- `ERROR — nothing was checked` (exit 2, no binary path given / not executable)

**Red control** (proves the check is not vacuous): run against a fake binary
(`/tmp/.../fake_silent.sh`, not committed) that reproduces the exact claimed
defect — exits 0 with empty stdout for the `print f64.sin(0.0)` case. Result:
`FAIL — 6 of 10 check(s) failed: print_form(interp:exit0) ...` (exit 1).

**Green** (real fresh build):

```
$ sh scripts/check/check-type-qualified-static-call-error.shs \
    /mnt/data/cargo-target-sinform/release/simple
PASS — 11 check(s), 0 failures
```

(11 = 5 forms x 2 lanes, minus 1 skip when interp already fails fast, plus
the 1 negative control — see script for exact accounting.)

## Verdict

CLOSED — false positive, not reproduced on a fresh build. Current behavior
(hard semantic error in both interpreter and native lanes) is the correct,
intended semantics per repo-wide `Type.method()` usage evidence. No source
changed. Landed: this bug doc + the reusable check script only.

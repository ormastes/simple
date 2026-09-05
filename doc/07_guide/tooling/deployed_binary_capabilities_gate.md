# Deployed-binary capabilities gate

`scripts/check/check-deployed-binary-capabilities.shs` — permanent post-redeploy
verification gate. Codifies the ad hoc capability probes run manually during
the 2026-08 redeploy campaigns (f64 builtins, `Result`/`Option` unwrap,
`sqrt`/`pow`/`sin`, `min`) into one fenced, repeatable check, so every future
redeploy is verified the same way instead of by hand.

## When to run

After **every** `bin/simple build bootstrap` redeploy, before trusting the
newly-deployed `bin/simple` for anything else:

```bash
sh scripts/check/check-deployed-binary-capabilities.shs
```

To verify a candidate build BEFORE deploying it (e.g. a fresh
`/mnt/data/cargo-target*/release/simple`), override the target binary:

```bash
SIMPLE_BIN=/mnt/data/cargo-target/release/simple \
    sh scripts/check/check-deployed-binary-capabilities.shs
```

`--selftest` additionally proves the oracle itself can detect a wrong value
(runs a probe against a deliberately-wrong expectation and confirms it is
reported as a mismatch) — run it once when changing the gate itself.

## What PASS proves

1. **Provenance** (default target only, not `SIMPLE_BIN` overrides): the
   deployed binary's mtime is not older than the newest commit touching
   `src/compiler_rust` — a stale binary FAILs outright here, since the gate's
   entire claim is "the deployed binary has current capabilities."
2. **Capability probes**, each run through the real CLI entry point
   (`"$BIN" file.spl`, never in-process) with code inside `fn main():` — top-
   level script statements bypass JIT codegen and silently fall back to the
   interpreter, which would make this gate pass against a broken JIT. Probes:
   `(16.0).sqrt()`, `Result.Ok(42).unwrap()`, `Option.Some(7).unwrap()`,
   `min(1.5, 2.5)`, `sqrt(16.0)`, f64 literal `16.0`, `(0.0).sin()`,
   `pow(2.0, 3.0)`, and an i64 positive control `42`. Every comparison is
   against captured **stdout content**, never exit code — `bin/simple run`
   exits 0 even after a fatal `error: semantic:`.
3. **Oracle sanity** (negative control): an undefined-identifier probe must
   produce `error:` on stderr; if it doesn't, the run ERRORs out rather than
   reporting a false PASS.

Verdict is always the last line of stdout: `PASS — <n> probe(s) checked`
(exit 0), `FAIL — ...` (exit 1), or `ERROR — nothing was checked` (exit 2,
zero probes run).

## Known call-form pitfall (found while authoring this gate)

`(0.0).sin()` (method-call form) is correct. The call-form spelling
`f64.sin(0.0)` silently prints **nothing** — no error, empty stdout — rather
than failing loudly. Use the method-call form for float builtins.

## Spec coverage: deliberately skipped

No `test/01_unit/tooling/deployed_binary_capabilities_spec.spl` was added.
This gate's entire value is exercising the real CLI entry point against a
real deployed binary process — exactly what in-process specs cannot do (see
`reference_in_process_specs_cannot_reach_jit.md`). Existing `*_gate_spec.spl`
files in `test/system/` only grep source text for expected strings; they
never spawn `bin/simple` as a subprocess against a real file, so that pattern
would not add coverage here either — it would just assert this script's own
text is present, which is vacuous. The gate script itself is the test.

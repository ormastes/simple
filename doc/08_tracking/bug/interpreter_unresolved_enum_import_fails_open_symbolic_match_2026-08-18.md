# Interpreter: unresolved enum import fails open — variant access and match work symbolically

Status: OPEN (advisory; found while sabotage-testing check-bootstrap-preflight.shs)
Date: 2026-08-18
Area: seed interpreter, import/type resolution

## Symptom (measured, not inferred)

A program importing a NONEXISTENT name from a real stdlib module runs to
completion with exit 0 and semantically "correct" output:

```
use std.binary_io.{ByteOrderX}          # ByteOrderX does not exist anywhere
fn order_name(o: ByteOrderX) -> text:
    match o:
        case ByteOrderX.LittleEndian: "little"
        case ByteOrderX.BigEndian: "big"
fn main():
    print(order_name(ByteOrderX.LittleEndian) + "," + order_name(ByteOrderX.BigEndian))
```

Under the current seed (`bin/simple run`, rebuilt 2026-08-18 06:12) this prints
`little,big` and exits 0. The import failure is only a WARN:
`[WARN] Failed to load imported types from ["std", "binary_io"]: ...`.
`ByteOrderX.LittleEndian` evaluates to a name-symbolic value that its own
`case` pattern then matches — even discriminating variants correctly — so an
entirely unresolved enum behaves like a real one.

## Why it matters

- Any T0 probe of the form "does this import/type resolve?" is VACUOUS under
  the interpreter: it passes when the import is broken. The preflight probe in
  `scripts/check/check-bootstrap-preflight.shs` was strengthened (two-variant
  discrimination) and its mutation proof had to sabotage the mapping, not the
  type name, because a wrong type name cannot make the run fail.
- Same fail-open family as `mir_unresolved_method_const0_fails_open_2026-07-28.md`
  and `case_bare_ident_is_irrefutable_binding_2026-08-01.md`, but this is
  interpreter-side import/type resolution, not MIR lowering.

## Expected

An unresolved imported type used as a value/pattern should be a hard error (or
at minimum make `run` exit nonzero), not a WARN followed by symbolic execution.

## Rejected selective-import candidate evidence (2026-11-03; no closure)

A candidate validation patch was prepared against source base
`deb089b0eae35329dcf8bcbb3782b483a6e79464`. The candidate file in its isolated
worktree was
`src/compiler_rust/compiler/src/hir/lower/import_loader.rs`, SHA-256
`45B1D8D6D52200F9A82ACB4B470EAFC254AE919267DE96880A1DBF15C92B2039`. This
source draft was rejected and is not included or proposed for landing.

The four focused tests did not execute. The first bounded attempt stopped
during setup because LLVM sys dynamic linking is unsupported in this Windows
configuration; zero test assertions ran. Attempt 3 failed during Rust harness
compilation after 174 seconds (rc 101), also with zero tests: the candidate
passed a `PathBuf` to a `String` set, and the sparse checkout reported 11
missing compile-time include-file references spanning fixtures and production
Simple sources. This is a candidate/build setup failure, not a semantic test
result. The retained attempt-3 receipt is
`C:/dev/p3new/selective_import_validation_20261103/unit_attempt_03/result.sdn`,
SHA-256
`191E2680CBE34FBB71CE2AF94D0CCE053B24C97361F895C472254BF39C58C13E`; its
stderr is `unit_attempt_03/cargo-no-run.log.err`, SHA-256
`B630ED9C5C1EAFC20DB5CAD39BE1F8A451FEF36B0C229583F388D81DB6660FBB`.

The four named focused tests—name validation, declarations and re-exports,
missing re-export and cycle-only names, and incomplete package graphs—remain
unexecuted. No retry or source repair is recorded here. The historical
2026-08-18 behavior has not been remeasured against this release; this issue
remains OPEN and unverified. Neither the rejected candidate nor its zero-test
attempts establish runtime closure, and the existing bug database status
remains open.

# MIR validity verifier (`MIRV-*`) and MIR lowering advisories

## What it prevents

Invalid MIR reaching a backend, where it shows up as a crash or wrong code far
from the cause: raw text/aggregate-to-narrow-scalar casts (the "ptr to i8" LLVM
crash), call arity and argument-type disagreement, missing block targets,
duplicate `Switch` cases, unknown enum variants, out-of-layout field indexes,
duplicate symbols, unit-typed storage.

- Verifier: `src/compiler/50.mir/mir_verify.spl` — one linear pass per function.
- Rule registry: `config/compiler/mir_verify_rules.sdn`; in-binary projection
  and level resolution: `src/compiler/50.mir/mir_verify_levels.spl`.
- Driver step: `CompilerDriver.verify_lowered_mir_v1`
  (`src/compiler/80.driver/driver_pipeline_lowering.spl`), called by both
  `lower_to_mir` entry points **only when lowering succeeded**.

## How it reports

Every rule lands warn-first (`lifecycle: warning`). A finding names rule id,
module, function, block, instruction and source span:

```
MIR verify [MIRV-002]: raw cast between text and narrow scalar: opaque<str> -> u8; ... (module m, fn f, block 2, inst 7) at path.spl:16:9
```

Warnings are capped per rule per build: the first 10 lines, then one count
line. Errors are never capped. The `mir_verify` pass receipt carries the
module and diagnostic counts (`SIMPLE_PASS_RECEIPT`).

## Two lowering advisories share the switch

`E-MIR-TYPE-Error` (an unresolved `HirTypeKind.Error` type erased to `i64` in
`lower_type`) and `E-MIR-MATCH-GUARD` (guard-count invariant of enum-match
lowering) are **advisories**, not verifier rules. At the default level they are
recorded in `MirLowering.mir_advisories` — never in `MirLowering.errors`,
because non-driver routes abort on `errors.len() > 0` and array/dict literal
lowering compares `errors.len()` around each element. The driver prints them as
capped warnings and records a `mir_lowering_advisory` receipt; other routes drop
them. `E-MIR-TYPE-Error` advisories are rate-limited to 3 per module + function
plus one summary line.

## Level switch

```
SIMPLE_MIR_VERIFY_LEVELS="MIRV-002=error,MIRV-005e=off,*=warning"
```

| level | effect |
|---|---|
| `error` | fatal; nothing is handed to a backend |
| `warning` | reported, build continues (default for every id) |
| `off` | not reported |

- `*` sets every id not named explicitly — **the `MIRV-*` rules and the two
  `E-MIR-*` lowering advisories**. `*=error` therefore turns the advisories into
  fatal lowering errors on every route (bootstrap, JIT, backend, SimpleOS tool),
  not just the driver. Name them explicitly (`*=error,E-MIR-TYPE-Error=warning`)
  to keep them advisory.
- Under `E-MIR-TYPE-Error=error` every occurrence is an error; there is no rate
  limit and no summary line.
- When every `MIRV-*` rule is `off` the verifier walk is skipped entirely
  (receipt `state=skipped`).
- The spec is resolved once per run. A malformed entry, an unknown level or an
  unknown id rejects the **whole** spec: every id keeps its registry default and
  the driver reports a build error. A typo never resolves to `off`.
- `SIMPLE_ASSURANCE_WARNING_PHASE` downgrades a verifier `error` one level. It
  does not downgrade a promoted lowering advisory.

## Adding a case

1. Add the record to `config/compiler/mir_verify_rules.sdn` and the same row to
   `mir_verify_rules()` (`mir_verify_rule_registry_spec.spl` pins the two).
2. Report it with `self.report("MIRV-xxx", ...)` in `mir_verify.spl`; build
   message text only on the failure path.
3. Add a must-fail and a must-pass example under
   `test/01_unit/compiler/50.mir/mir_verify/`.
4. A new lowering advisory uses `self.advisory(code, message, span)` and must
   be listed in `mir_lowering_advisory_ids()`.

## Known limits

- `MIRV-005e` is "no definition anywhere in the function", not dominance.
- Cross-module callees are not checked (identity is resolved at link time).
- `config/compiler/mir_verify_baseline.sdn` is a reference measurement, not an
  enforced ratchet.
- Promotion of any rule to `error` needs a full-closure zero-hit run first.

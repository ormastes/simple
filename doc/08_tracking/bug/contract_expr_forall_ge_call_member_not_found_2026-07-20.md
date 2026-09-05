# Bug: `ContractExprKind.Forall` (enum variant) and `ContractExpr.ge`/`.call` (static methods) report "not found" from outside the module even though they are defined in source, while sibling members (`.gt`, `.Ge`, etc.) resolve fine

- **Date:** 2026-07-20
- **Status:** open
- **Area:** `src/compiler_rust/lib/std/src/verification/models/contracts.spl` (`enum ContractExprKind`, `class ContractExpr`), exercised via `test/00_formal_verification/compiler/unified_attrs_spec.spl`
- **Binary:** reproduced on `bin/release/x86_64-unknown-linux-gnu/simple`, which currently prints the Rust-seed bootstrap warning — likely a seed-interpreter symbol-table/dispatch defect; not independently re-verified on a genuinely self-hosted binary.

## Symptom

`unified_attrs_spec.spl`, 4 of 5 examples fail, each on the FIRST statement of the test body (so later assertions in the same block never execute):

1. "classifies operators and renders summaries" (line 8):
   ```
   expect(contracts.ContractExprKind.Forall.is_quantifier()).to_equal(true)
   ```
   ```
   semantic: unknown variant or method 'Forall' on enum ContractExprKind
   ```

2. "tracks requires, ensures, invariants, and termination" (line 22):
   ```
   contracts.ContractExpr.ge(contracts.ContractExpr.variable("n"), contracts.ContractExpr.int_val(0))
   ```
   ```
   semantic: unknown static method ge on class ContractExpr; did you mean 'gt'?
   ```

3. "rejects impure calls in contracts" (line 59):
   ```
   contracts.ContractExpr.call("read_file", [contracts.ContractExpr.variable("path")])
   ```
   ```
   semantic: unknown static method call on class ContractExpr
   ```

4. "can be marked public" (line 74): same `ge` failure as #2.

## Root cause direction (unproven, filed as suspected cause)

All three named members DO exist in source:
- `ContractExprKind.Forall` — `contracts.spl:38` (`# forall x: T. expr`), a plain no-payload variant alongside `Eq`, `Gt`, `Ge`, `Len`, etc.
- `ContractExpr.ge` — `contracts.spl:439-440` (`fn ge(left: ContractExpr, right: ContractExpr) -> ContractExpr: ContractExpr.new(ContractExprKind.Ge).with_children([left, right])`), directly adjacent to `gt` (line 436-437), which the error message itself confirms IS resolvable ("did you mean 'gt'?").
- `ContractExpr.call` — `contracts.spl:442-445`, directly adjacent to `ge`.

None of these methods use the `static` keyword explicitly (they're plain `fn name(...)` inside the class body with no `self`/`me` parameter, same pattern as `ContractExpr.new`, `.true_()`, `.variable()`, `.int_val()`, `.result()`, `.eq()`, `.lt()`, `.le()`, `.gt()` — all of which DO resolve, since the test bodies reach past them via chained calls in the same statements without erroring on those names specifically). So "missing `static` keyword" alone does not explain the asymmetry between `gt` (works) and `ge` (fails), or between other zero-arg enum variants (untested past the first failure) and `Forall`.

Two candidate mechanisms, neither confirmed:
- A method/symbol-table collision specific to the short names `ge`/`call`/`Forall` — e.g. `ge`/`gt`/`lt`/`le`/`eq` are also the mnemonic names of comparison operators, and `call`/`forall` are generic/reserved-adjacent words; if the interpreter reserves these names for an internal protocol (operator-overload dispatch, callable-object protocol, quantifier grammar) when resolving a **static** method/variant from **outside** the defining module, that could explain why intra-file self-references (e.g. `ContractExpr.new(ContractExprKind.Ge)` from within `ge`'s own body, which works — it's how `ge` is defined) succeed while external `contracts.ContractExpr.ge(...)` / `contracts.ContractExprKind.Forall` fail.
- A partial/cut-off member-registration bug specific to package-qualified (`module_alias.Type.member`) access, as opposed to unqualified same-file access.

## Impact

`FunctionContract`/`ContractClause`/`ClassInvariant` contract-building code (used for `requires`/`ensures`/invariant clauses) cannot construct `>=` comparisons or function-call contract expressions, and cannot build `forall` quantifiers, when called from outside `verification/models/contracts.spl` itself — i.e. from any real caller, since the whole point of the class is to be used elsewhere. This blocks 4 of 5 example groups in `unified_attrs_spec.spl`.

## Suggested fix direction

Needs actual interpreter/semantic-checker instrumentation to compare symbol-table entries for `gt` vs `ge` and for `Ge`/`Gt`/`Eq` vs `Forall` at the point of external qualified-name resolution — out of scope for a source-level test-triage fix. File for interpreter/semantic-checker follow-up.

## Repro

```bash
bin/release/x86_64-unknown-linux-gnu/simple test test/00_formal_verification/compiler/unified_attrs_spec.spl --no-session-daemon
```
4/5 examples fail as above.

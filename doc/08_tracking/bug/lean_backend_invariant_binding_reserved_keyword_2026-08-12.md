# Lean backend local binding collides with reserved `invariant`
## Closed 2026-09-16 — fix section: local renamed to invariant_text; parse error resolved

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

Date: 2026-08-12

## Reproduction

`src/compiler/70.backend/backend/lean_backend.spl` declared `val invariant =
self.invariants.join(" ∧ ")` in `FunctionContract.to_lean_pure_state_spec`.
The Rust and self-hosted lexers classify lowercase `invariant` as the contract
keyword, so parsing the declaration failed with:

```text
Unexpected token: expected pattern, found Invariant
```

## Fix

The local is now named `invariant_text`; generated theorem text is unchanged.
This keeps the backend source within the language's reserved-identifier rules.


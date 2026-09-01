# Interpreter: the BDD negation link `.not` and the arg-less nil matchers are unsupported (2026-09-01)

Status: OPEN. Found while fixing the NATIVE half of the same surface
(PR #212, `fix/suite4-hir-group`); deliberately not fixed there, because it is
a different code path with a different failure mode and its own blast radius.

## Symptom

Under `simple run` (interpreter), on a seed built from `origin/main`
`c0cae452481`:

```
expect("hello world").not.to_contain("zzz")
  -> semantic: undefined field: unknown property or method 'not' on String
expect(v).to_be_nil                       # v = nil
  -> semantic: undefined field 'to_be_nil': cannot access field on value of type 'nil'
expect("present").to_not_be_nil
  -> vacuous expect: expect(present) was never consumed by a matcher
```

The third is the most dangerous of the three: it is diagnosed as vacuous rather
than crashing, which is exactly the "asserts nothing" class the vacuous-expect
guard exists to catch — so the guard is doing its job, but the matcher itself is
simply missing.

## Blast radius

`.not.<matcher>` has **305** call sites in `test/**` on this tree, 175 of them in
the 39 specs that were failing the native lowering. `to_be_nil` in its
paren-less form has 46. Every one of those assertions is currently either an
interpreter error or vacuous.

## Not caused by, and not fixed by, PR #212

Measured on BOTH a pristine `origin/main` seed and the patched seed, rc read
into a variable on the line after the invocation, never through a pipe: the
three diagnostics above are byte-identical on the two binaries. PR #212 changes
`hir/lower/stmt_lowering.rs` only, which the interpreter path does not use.

Its reproduce artifact is therefore a compile-only fixture,
`test/fixtures/compile/bdd_negated_matcher_chain_lowering.spl` — deliberately
NOT named `*_spec.spl`, because shipping it as a spec would ship three
guaranteed-red examples for a defect that spec does not own.

## Where the fix belongs

`compiler/src/interpreter_call/bdd.rs` (the `"expect"` arm) and
`compiler/src/interpreter_method/special/types.rs`. The native side's mapping in
`hir/lower/stmt_lowering.rs::try_lower_bdd_matcher_statement` — peel `.not` /
`.not_()` off the receiver, treat `to_not_<x>` as a negated `to_<x>`, and route
`to_be_nil`/`to_be_none` and `to_contain` — is the shape to mirror. It must stay
a mirror: the two paths silently disagreeing about what a matcher asserts is the
divergence class PR #157 closed.

## Do NOT "fix" this by editing the 305 call sites

They are correct source. The matcher surface is documented and the native path
now honours it.

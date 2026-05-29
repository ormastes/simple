# Generic BTree Spike Parse Failure

The former active spike spec at `test/spike/generic_btree_spike_spec.spl`
failed before execution:

```text
parse error: Unexpected token: expected expression, found Dot
```

The failing reproducer is preserved as
`test/fixtures/repro/language/generic_btree_spike_spec.spl.fixture` so broad
SPipe discovery does not treat it as passing or release-blocking executable
coverage. Promote it back to `test/feature/language/` only after the parser
accepts the generic static-call form under test.

Smaller scratch reproducers showed related SPipe parser-sensitive syntax:
`Container<i64>.wrap(42)` and `Pair<i64, text>(...)`. Single-parameter generic
constructors, generic functions, and generic instance method calls were promoted
to active SPipe coverage in `test/feature/language/generic_repro_spec.spl`; the
static generic method-call and multi-parameter constructor forms remain tracked
here until SPipe parsing accepts them.

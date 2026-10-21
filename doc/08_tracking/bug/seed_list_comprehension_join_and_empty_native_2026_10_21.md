# Seed list comprehensions lose native values and contaminate join typing

- Canonical ID: `seed_list_comprehension_join_and_empty_native_2026_10_21`
- Status: open; bootstrap workaround only.
- Recovery reference: `400bd5d1983`.
- Workaround owner: Codex HTTP/MIR diagnostic lane.
- Underlying repair owner: compiler HIR expression lowering, pending.
- DB reconciliation: pending a qualified self-hosted `check-dbs` command.

The exact Windows bootstrap seed SHA256
`32014b3401e3cb76aec44acb475a22f2385fefcd1d19ab71049e52d633356825`
rejects `serialize_mir_enum_indexes_v1` in the full Phase2 namespace. With
`SIMPLE_SEED_RETURN_TYPE_DEBUG=1`, the actual failing function is named before
the optional-`Add` diagnostic. The original 127-module MIR-owner closure
passes, so that isolated closure did not reproduce the full-project failure.

The untyped comprehension's receiver becomes ANY. In the full namespace,
method return fallback can choose `Thread.join() -> i64?`; concatenation then
fails the optional BoxInt arithmetic guard. An explicit `[text]` annotation
clears HIR, but is insufficient: the real native two-module control emits `[]`
instead of `[1,2]`. The unpolluted comprehension also emits `[]`. The underlying
HIR expression owner lacks a list-comprehension handler and its lenient
unsupported-expression fallback returns Nil/ANY. It must preserve real values
and typed receivers rather than accepting empty output.

The scoped workaround replaces the nine MIR JSON comprehensions with explicit
typed arrays and ordered `for`/`push`, including integer exit-block identities.
All affected source blocks carry this canonical ID. No metadata, source module,
assertion, provider requirement, or array value is omitted. Speculative earlier
hexadecimal-slice unwraps are reverted; they were not the causal boundary.

Actual fullscope pre/post evidence uses the same frozen seed, all six source
roots, bootstrap entry, and a private copy of the terminal campaign cache:

```text
before: compiled=2 reused=1434 failed=1
        lowering error in function serialize_mir_enum_indexes_v1: optional Add
after:  compiled=3 reused=1434 failed=0
```

The post run reaches linking and fails for `rt_shell_exec_tuple` and
`rt_shell_exit_code`; it is not a successful executable or Phase2 admission.
Logs are retained privately under `build/mir-json-fullscope/trace-baseline.log`
and `trace-fixed.log` in `D:/dev/simple-http-client-imports-20261021`.

Removal requires a repaired producer to run the original untyped and typed
comprehension controls with nonempty expected values under optional-join
pollution, then compile the original fullscope MIR JSON source and pass the
serializer regressions. A compiler/link success alone cannot retire this
workaround. The underlying compiler bug remains open.

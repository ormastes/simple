# MIR loses named owner on a chained method result

Status: OPEN. Tagged source workaround and regressions AUTHORED_UNEXECUTED.

Producer1fcd9a20 (compiler873ea2e4), frozen29223ded5Postgresclosure, normal
LLVM12jobs: HIR has zero fatal records; MIR fails with unresolved method
`equals` at common/bytes/span.spl116. The expression
`self.slice(0, prefix.span_len).equals(prefix)` calls declared ByteSpan methods,
and `slice` explicitly returns ByteSpan. No Postgres binary is produced.

Workaround: bind exactly that sliced result to a typed ByteSpan local before
calling equals. The guard, slice arguments, equality implementation, values,
and public API remain unchanged. Tag links this bug; no recovery commit is
claimed. Remove workaround only after the original chain compiles and runs.

Three value scenarios/five assertions cover offset spans, unequal/longer
prefixes, and empty prefix boundaries. Native original and typed fixtures
under test/fixtures/compiler/chained_named_receiver_owner provide the direct
reproduction and three runtime checks. All executable qualification is pending.
The permanent compiler owner must retain the declared result type of a nested
method call, with an adjacent negative unknown-method rejection regression.

Second source workaround candidate: retain an explicit typed ByteSpan receiver before slice as well as the typed result; actual first result-only variant generated string-slice calls and failed its first equality check despite a nonempty object and successful link. Receipt `/home/ormastes/simple-phase4-web-a0-parallel-20261010/leaf-fixtures/typed-span/evidence.json`; disassembly diagnosis adjacent. New receiver candidate UNEXECUTED; original valid chained control remains unchanged.

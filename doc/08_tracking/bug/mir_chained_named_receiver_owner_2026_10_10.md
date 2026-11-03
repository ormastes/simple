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

Receiver/input/result annotation candidate `df4abc1a2` also fails actual runtime: object16696B, link0, run1, emitted string-slice callee remains wrong. No recovery claimed. Permanent compiler dispatch repair is required; no further unchanged source spelling retries.

**Revalidated 2026-11-02: still plausible because OPEN. Tagged source workaround and regressions AUTHORED_UNEXECUTED; no merged fix commit with a passing regression is cited in this doc.**

**2026-11-03 triage (groupB):** a single-module MIR lowering of the same shape
(`self.slice(0, p.span_len).equals(p)` on a struct with `[u8]` data) dispatches to
`Struct.slice` / `Struct.equals` with no `spl_str_slice` (spec
`test/unit/compiler/mir/chained_named_receiver_owner_spec.spl`, passing). The failure
therefore needs the cross-module closure (`common.bytes.span` imported into the
Postgres build): the inner `slice` resolves as `resolution_is_unresolved` and falls
into the erased text-slice fallback at `method_calls_literals.spl:3702`. Needs a
stage3 multi-module repro; workaround retained.

**2026-11-03 (sonB): deferred, concrete blocker.** Single-module spec passes (see groupB triage); failure is cross-module: inner `self.slice(..)` resolves Unresolved and the result local carries no struct owner, so `.equals` is unresolved. Candidate fix site: after the inner call is lowered in `method_calls_literals.spl` (~3640-3700), record the callee HIR return type (ByteSpan) on the result local (`local_hir_type`) so the outer call finds its owner. Needs a multi-module (common.bytes.span + importer) repro under stage3 to write the failing spec; not safe to edit blind.

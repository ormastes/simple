# `.?` exists-check on an `i64?` yields the payload / nil instead of a bool

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
the ratified contract: `.?` returns `T?` (payload if present, nil if absent),
never `bool`. The expectation in this report (`expect r.? to_equal true`) is
what is wrong, not the compiler. See "Re-triage 2026-08-08" at the bottom.
**Original status:** open
**Found:** 2026-08-01, by de-vacuum-ing `test/unit/compiler/codegen/static_method_spec.spl`
**Lane:** vacuous-spec audit
**Engine:** tree-walking interpreter (`bin/simple_seed test`) — PROVED there; other lanes untested

## Symptom

`opt.?` on a value of declared type `i64?` does not evaluate to a `bool`. It
evaluates to the **payload** when present and to **nil** when absent. Any code
that treats `.?` as a boolean therefore branches on a non-boolean, and any
`if opt.?:` is testing truthiness of the payload rather than presence.

Note the sharp edge: for a present value of `0`, "payload as truthiness" and
"presence" disagree.

## Reproduction (PROVED)

    use std.spipe.*

    class GParser:
        static fn parse_int(s: text) -> i64?:
            if s == "42":
                42
            else:
                None

    describe "static method gaps":
        it "static returning Option some":
            val r = GParser.parse_int("42")
            expect r.? to_equal true

        it "static returning Option none":
            val r = GParser.parse_int("x")
            expect r.? to_equal false

Transcript:

    ✗ static returning Option some
        expected 42 to equal true
    ✗ static returning Option none
        expected nil to equal false

So `.?` returned `42` (the payload) and `nil` (not `false`).

## Relation to existing notes

This is adjacent to, but not the same as, the previously recorded
"seed `.?` lowers to BOOL not T?" observation — here the observed result is the
opposite direction: no bool is produced at all. Both cannot be right; the
lowering of `.?` needs a single documented contract and a spec that gates it.

## Why this was invisible until now

`static_method_spec.spl` had an `it` block named "handles static method
returning Option" whose body was a never-compiled source string followed by `0`.
It reported PASS. The behaviour above has presumably been wrong the whole time.

## Not fixed here

Recorded, not repaired. Do NOT weaken the expectation to make it pass.

## Re-triage 2026-08-08 — INVALID, premise contradicts the ratified contract

This report's own transcript is the correct behaviour. `.?` returning `42` for
a present `i64?` and `nil` for an absent one IS `T?`, which is exactly what the
operator is specified to do. The report's "Expected" column assumed `bool`.

That `bool` assumption was already adjudicated and rejected. The sibling report
`optional_query_operator_identity_passthrough_2026-07-20.md` filed the same
"`. ?` should return bool" claim and was closed **superseded / RESOLVED** on
2026-08-02 (`codex-par-optionquery`, "no boolean-conversion implementation
accepted"), on the grounds that `T?` is the contract in three independent
places. This report was filed 2026-08-01, one day before that ruling, and never
got the memo — which is exactly the stale-backlog failure mode this triage pass
exists to catch.

Reproduced 2026-08-08 on the tree-walk interpreter
(`SIMPLE_EXECUTION_MODE=interpreter bin/simple run`), using this report's own
`GParser.parse_int` class verbatim:

    some.? = 42
    none.? = nil

Binary: `bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`, which
prints the Rust bootstrap-seed banner; no pure-Simple self-hosted binary is
deployed on this host.

**Already gated, so no new spec is needed.** The contract has a canonical spec:
`test/03_system/feature/usage/exists_check_value_return_spec.spl` ("Existence
Check Value Return (.? -> T?)", feature #2100-VALUE-RETURN), whose header states
"After the `.?` return-type change, the operator returns `T?` instead of
`bool`." A regression spec asserting the `bool` behaviour would directly
contradict it.

**The one real finding in this report survives** and is NOT closed by this:
`test/unit/compiler/codegen/static_method_spec.spl` had an `it` block whose body
was an uncompiled source string followed by `0`, and reported PASS. That vacuity
is a genuine defect of the spec corpus; it simply is not evidence of a `.?` bug.

**Note for the reader who lands here next:** the neighbouring
`bare_optional_in_condition_position_wrong_branch_2026-08-01.md` is the report in
this cluster that is still live. It is the INVERSE issue — a *missing* `.?` in
condition position being silently accepted — and it is unaffected by this
closure.

# Known tool defects (OPEN) — discovered by the validation corpus

These `.spl` files are **reproducible repros of real defects** in the deployed
pure-Simple compiler (`bin/release/x86_64-unknown-linux-gnu/simple`), found while
standing up the tool-qualification corpus. Each is a program that a
safety-critical (DO-330 Criterion-1) tool **should reject** but which the
deployed binary **silently accepts**. That is failure mode **TOR-FM-02**
(silent accept of a bad program) from the tool qualification plan.

They are **NOT** gated by `run-tool-qual-corpus.shs` — a perpetually-red gate is
not the goal. They are durable, hand-verifiable evidence and seed the plan's
`known_problem/` category / `tool_known_problems` ledger (plan §3.1). Reproduce
any of them with:

```
bin/release/x86_64-unknown-linux-gnu/simple run <file>.spl ; echo "exit=$?"
```

| Repro | Should happen | Actually happens (deployed binary) | Severity |
|---|---|---|---|
| `arity_too_many.spl` | reject: `add/2` called with 3 args | accepted, extra arg dropped, prints `3`, exit 0 | high |
| `arity_too_few.spl` | reject: `add/2` called with 1 arg | accepted, prints `1`, exit 0 | high |
| `arg_type_mismatch.spl` | reject: text passed where `i64` expected | accepted, prints GARBAGE (raw text pointer as int, e.g. `6295919127139`), exit 0 | **critical (memory/type-safety hole)** |
| `undefined_type_annotation.spl` | reject: `val x: Nonexistent` names no type | accepted, prints `5`, exit 0 | medium |
| `nonexhaustive_match.spl` | reject/trap: `match` has no arm for `E.B` | accepted, `f(E.B)` returns `0`, exit 0 | high |

For contrast, the following ARE correctly rejected (they live in `../negative/`
and pass the gate): undefined variable, unknown struct field, undefined
function call, parse error.

**Interpretation.** Name resolution rejects *unknown* symbols/fields/functions,
but the type/arity checker does **not** reject *arity* mismatches, *argument-type*
mismatches, *unknown type annotations*, or *non-exhaustive matches* — these reach
codegen and execute with wrong/garbage semantics. The `arg_type_mismatch` case is
the most serious: it is an unsound accept that reads a text pointer as an integer,
exactly the class of latent product defect DO-330 tool qualification exists to
prevent. Until each is fixed (or waived with justification), the tool is **not**
qualifiable at Criterion 1 for the required function TOR-F2 (type-check).

# Bare names that must not become a silent variant test

Requirement: `REQ-SSPEC-COMPILER`.

Executable specification: `test/01_unit/compiler/50.mir/bare_variant_untyped_subject_reject_spec.spl`.

## Fixture

The specification parses and lowers a provider (`lib.data`), a glob re-export
facade (`lib.facade`), and a consumer (`app.main`) through HIR and MIR in
process. The provider includes `Op`, `Inst`, `Kind`, and `Cmp`; `Return` belongs
only to `Kind`, while `Eq` belongs to both `Op` and `Cmp`.

## Scenarios and executable assertions

| Scenario | Fixture behavior | Oracle |
| --- | --- | --- |
| Known non-enum subject | Match an `i64` with bare `Var`, then read `Var + 1`. | Collected diagnostics contain neither `no variant`, `enum match`, nor `unresolved`. |
| Known enum subject does not own the name | Match `Inst.Bin(d, op)`, then match the `Op` payload with bare `Return` and read `Return == Op.Eq`. | Collected diagnostics contain neither `'Return'`, `ambiguous`, nor `unresolved`; MIR contains function `k2` and exactly two `ematch_arm` blocks. |
| Untyped subject, unique variant name | Match an untyped parameter with bare `Lt`, owned only by `Op`. | Collected diagnostics contain neither `B5b`, `unreachable match arm`, nor `ambiguous`. |
| Untyped subject, shared variant name | Match an untyped parameter with bare `Eq`, shared by two enums. | Collected diagnostics do not contain `ambiguous`. |

The known-enum scenario has a structural MIR oracle: only the outer `Inst.Bin`
and `Inst.Nop` arms may emit enum variant-test blocks. `Return` must bind the
`Op` payload, so the nested match must add no enum variant test. Selecting
the unrelated `Kind.Return` discriminant would add a third `ematch_arm` block
and fail this assertion. Requiring the function to exist prevents empty MIR
from satisfying the block-count check.

The diagnostics helper retains its text-returning interface; a second helper
exposes the same lowering result as `(MirModule, text)` for structural checks.
The scenarios describe warning behavior, but stderr warnings are not captured
or asserted by this specification. The untyped-subject scenarios currently
assert diagnostics only; they do not establish variant or binding MIR shape.

## Verification status

**NOT EXECUTED**: a qualified self-hosted CLI runtime is unavailable in the
current validation environment. No runtime PASS is claimed, and the Rust seed
was not used as a substitute. Static diff validation is separate from execution
of these compiler assertions.

# Result unwrap accepted a mismatched nominal declaration ID

Status: source fix authored; runtime UNRUN. Bug database registration pending;
no bug-add command was executed because compiler execution is not authorized.

`lower_result_unwrap_core` previously accepted the Struct/Class/Enum declaration
returned for a Named symbol's numeric table key without comparing that record's
own ID. A malformed/remapped symbol-table entry therefore selected another
nominal owner, allowed runtime payload access, and could attach that owner's
record metadata. This is a constructed HIR integrity failure, not attribution
of the historical unexplained driver diagnostics or collector group 108.

`REQ-ENUM-RESULT-NOMINAL-IDENTITY`: require declaration.id == requested symbol.id
before accepting a nominal Result payload on unwrap or unwrap_err. Retain the
existing fatal unsupported-payload diagnostic and reject before receiver
lowering. Do not change valid metadata, erased Any handling, default forms,
or runtime payload ABI.

Regression: `test/01_unit/compiler/mir/result_nominal_identity_unwrap_spec.spl`.
Manual: `doc/06_spec/01_unit/compiler/mir/result_nominal_identity_unwrap_spec.md`.
The four scenarios were authored before production editing; fixture identifier
cleanup followed. The guard has constant cost and introduces no scan,
allocation, runtime call or ABI change. These are source observations, not
measured performance evidence.

Independent source review pending. Historical enum ledger remains open:
groups 99 and 108 lack precise current failure attribution; 111, 117 and 120
lack a confirmed unsupported current receiver. Landed PassScope/collector/Dict/
coherence fixes are not redone. Optional group 116 has a separate source-GO
packet with runtime still UNRUN. This patch closes none of those unexplained
groups by inference and does not establish all-enum completeness.

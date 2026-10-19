# Optional enum payload owners

Authored companion for `test/01_unit/compiler/mir/optional_enum_payload_owner_spec.spl`.
Execution and generated documentation: UNRUN for this follow-up.

Existing scenarios lower real source through HIR and MIR: explicit Some keeps
the declared scalar/nominal owner, while wrong primitives, foreign record
owners, raw optional carriers, and optional-to-mandatory mismatches reject.
Nominal-record nil comparisons retain their prior contract.

REQ-ENUM-FRAME-OWNER adds three record-field projection scenarios:

1. Unwrap a `Frame?` field and place the resulting Frame in a mandatory payload:
   require clean HIR/MIR lowering and a produced function.
2. Pass the same field without unwrapping: require a payload mismatch.
3. Unwrap an identically shaped `OtherFrame?` field: require a payload mismatch
   because its nominal owner remains foreign.

These checks preserve the payload boundary; they do not grant compatibility
from equal record layout or optional carrier representation.

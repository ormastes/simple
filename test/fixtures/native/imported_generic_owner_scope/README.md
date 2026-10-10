Imported generic owner scope regression

Status: AUTHORED_UNEXECUTED. This is a HIR/type-authority fixture; main returning zero is not runtime qualification of field reads.

Require both imported Channel and Packet to lower without unresolved Op/Cpl diagnostics. Inspect the canonical owner field map: operation/item/backlog must contain owner TypeParam Op, completion owner TypeParam Cpl, and packets Packet<Op>. Consumer decoy structures must not replace those binders. Concrete signatures and field readers must resolve i64; compiled field-read execution requires a separate actual construction fixture before admission.

The repair also must restore the consumer scope after imported field projection and preserve imported non-generic field dependencies. Existing imported_generic_fields remains the non-generic control.

`construction.spl` is a separate AUTHORED_UNEXECUTED runtime gate. It constructs Packet<i64> and Channel<i64, text> and checks eight concrete field/container/optional values with nonzero failure exits. Require actual object publication, compatible runtime link, execution exit zero, empty stdout and empty stderr. Do not infer this gate passes from main.spl's type-only success. Constructor specialization and optional boxing failures remain real blockers if this gate exposes them.

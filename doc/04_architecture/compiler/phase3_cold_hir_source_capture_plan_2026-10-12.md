# Cold HIR source capture plan

The bounded cold capture path needs source authority before it opens a full HIR
body. `driver_cold_hir_source_capture_plan_v1` consumes the real compilation
context and the existing cold/full-inventory configuration. In one owned scope
it reads the selected immutable source-inventory generation, checks the SCV
snapshot provenance and receipt, reads selected snapshot rows, and validates the
canonical generation text. It never substitutes the moving `CURRENT` pointer.

The source validators are shared with the retained typed-receipt path. That
path calls the global validator and each source-row validator at its original
check points. Physical alias byte checks, first-physical body lookup and
independent ABI failure collection keep their original order and behavior.

The new factory selects the first row for each physical source, while validating
every later logical alias's bytes. Full-inventory source/physical counts are
checked before the per-source target CFG receipts. Only compact
`DriverColdHirModuleInputV1` rows and selected digest/generation metadata escape
through a freshly allocated Result carrier. Inventory text, complete decoded
generation and source indexes remain scratch. The wrapper refuses active or
paused parent ownership and closes only its own scope.

This plan is source authority input, not a transformed-stage token. A public
plan constructor, replacement row or copied digest does not authenticate a HIR
body. The production compilation owner must bind the returned original capture
to its actual resolved/weaved stage and call the existing complete-body cold
consumer at the original capture point. It must preserve independent ABI
failure collection and publish ctx receipts/emissions only after all required
captures succeed. This source factory currently has no production activation.

Four new compiled-spec examples cover active/paused parent refusal, actual
physical alias byte binding and a coherent snapshot hash whose row contradicts
the pinned generation. Existing retained cold-receipt examples exercise the
shared delegation. Compilation/execution and full SCV/native integration are
pending. Source review and owned scope structure establish no RSS improvement.

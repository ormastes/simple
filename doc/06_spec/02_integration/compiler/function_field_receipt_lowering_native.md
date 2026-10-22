# Concrete function-field receipt bridge regression

Status: UNRUN. Production source and native fixture proposed; no proof or runtime PASS is claimed.

Executable: `test/fixtures/compiler/function_field_receipt_lowering_native.spl`. Build its actual production import closure with the exact pure producer, matching runtime, strict no-stub/no-delegation controls and independent admitted cache. Run in a fresh process with `SIMPLE_COMPILER_PHASE_PROFILE=1`. Acceptance requires exit zero, `PASS function_field_receipt_lowering_native`, and an emitted `[nominal-owner] function-field-return field=call_fn` receipt with present numeric HIR/MIR/operand discriminants. A marker without the receipt does not demonstrate that these private helpers ran.

The fixture invokes the actual parser, HIR lowerer and MirLowering on a function-valued record field call. It checks no lowering errors, a nonempty probe body, and a real raw indirect call with one argument/parameter, I64 return and valid destination. The receipt branch executes both private concrete enum projection helpers from the newly compiled target source. It does not copy their implementation. Run a second fresh process with profiling unset/0 to check the same MIR assertions succeed and no function-field receipt appears; this also guards the unchanged diagnostic gate.

The existing source-ownership fence is updated because it previously required the broken generic wrapper. That fence is supplemental and cannot replace native execution. The existing `native_function_field_signature_owner` fixture remains the broader provider-owned Result/Array/record regression and should run with a repaired actual producer/profile enabled to cover nested receipt branches.

Whole generic/memory intensive validation and Phase3 object checks remain independent requirements. This fixture alone does not qualify explicit generic argument transport throughout the compiler.

# C4 dictionary region interface

Status: frozen interface contract; dictionary provider, compiler capture/planner, and actual HIR root integration are planned or in progress. This document supplies no runtime PASS or full SOURCE admission. Acceptance scenarios below are UNRUN.

Consumer integration: [HIR region root construction](c4_hir_region_root_integration_v1.md).

Provider: c4_region_provider_abi. Compiler owner-phase capture/emitter/planner: c4_result_cfg_helper. Transform owns compile-account plumbing and existing call/enum captures; architecture owner owns later HIR root integration. No edits overlap active pin or ELF work.

Native operations13 birth,14 put,15 remove. Facades source_region_dict_new_v1(context,descriptor,capacity), source_region_dict_put_v1(context,dict,key_bits,value_bits), source_region_dict_remove_v1(context,dict,key_bits) all return Result<i64,SourceRegionErrorV1>. Birth returns ordinary tagged dictionary identity. Mutations return ordinary success/removed flag0/1; epoch advances internally. Existing separately prepaid stamp4 supplies an epoch when needed. No flag/epoch packing, new result record or mutable last-result accessor.

Descriptor [1,4,64,2,table,1]. Rows [0,8,1,0] raw-i64 key and [8,8,2,representation] exact Struct value, representation1 raw or2 tag1. Extent64 is header size; row offsets refer to32-byte entries, never header GEP. Native sizeof/offsetof validate grammar. Typed raw key comes from actual pre-box HIR lowering local. Operation16 get(control,generation,expected_epoch,dict,raw_key,work) returns0 absent, positive non-null Struct bits or negative fixed error. Facade returns Result<Option<i64>,E> using canonical Option codecs. Existing absence semantics must be preserved explicitly; never reinterpret absent0 as Struct.

Birth attaches existing owner control+generation before publication. Put/remove validate typed same-region children and prepay lookup/growth/tombstone/copy/retirement work/fields/bytes before mutation. Rehash preserves association. Foreign/preexisting children refuse unchanged. Same-value writes advance epoch. Alternative unclassified writes reject before store. Existing registry only; SOURCE-only backing prefix may hold association with no ordinary header/entry growth, subject to review of lifetime and bound bridge.

The required MirLowering implementation records SourceRegionDictionarySiteV1 before boxing: owner function/block/instruction, operation, exact dictionary/key/value/result locals, original HirType key/value and canonical codec/descriptor facts. Finalization binds actual emitted sites/operands/runtime ABI. No source SymbolId fabricated for runtime builtins; no name-based admission or after-the-fact typed Copy birth inference.

Compile-time capture budget is the actual compiler invocation account: required prepare_source_region_request_v1 compile_account parameter, plan field, lowerer field installed before replay and cleared at request exit. Same account funds capture/finalization/verification before growth. Generated runtime SourceRegionContext.account is separate and cannot fund compilation.

First fixture births dictionary+Child, inserts then retrieves child through actual typed read, captures stamp, mutates retrieved alias and observes Stale. Include remove0/1 semantics, same-value write, rehash, foreign child, and fuel-one-short no-change controls. HIR still needs text-key dictionaries, optional Scope.parent, enum Scope.kind, rich symbol types/arrays and immutable text authority. Full SOURCE is not admitted by this milestone.

The required SOURCE-selected owner lowering emits private typed dictionary operations BEFORE ordinary boxing. Activation requires actual request membership/current-function receipt and compilation account; account presence alone is insufficient. Exact i64/Struct validation precedes birth. Ordinary lowering is unchanged. Preserve key/value expression order, .set receiver-alias result, and remove boolean. No rt_value_int_wide fragment is emitted for SOURCE keys; include i64 min/max fixtures.

# C4 compiler allocation and write choke points

Status: inspected source at `1dc81da08c2`; implementation and execution OPEN.
This inventory does not certify a backend or admit SOURCE authority.

## Representation prerequisites

`50.mir/mir_instruction_kinds.spl` separates `Alloc`, `Store`, `StoreGlobal`,
`Aggregate` and `SetField`. There is no MIR `IndexSet` instruction: container
writes also travel through calls. `SetField` carries a numeric slot and operands,
not a typed slot descriptor or region identity. `MirTypeKind.Struct/Enum` retain
symbols; their type definitions must supply exact field/variant edge kinds.
Unknown types, raw pointers, erased calls and unavailable definitions cannot
establish scalar or certified immutable storage.

## Finite coverage matrix

All rows remain uninstrumented for C4 in this revision.

| Route | Actual owner/choke point | Required operation |
|---|---|---|
| LLVM aggregate birth | `70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl`, aggregate translation (`rt_alloc`, `rt_array_new/push`, initializer `emit_store`) | Region allocation before any initialization or alias publication; typed incoming edges for every initializer |
| LLVM alias field | Same file, `llvm_set_field_impl` | Atomic provider typed-slot write, including same-value stores |
| LLVM pointer/global | `_MirToLlvm/core_codegen.spl::translate_store`, `translate_store_global_at` | Resolve allocation owner, distinguish local/control slots from observable graph writes; reject unclassified destinations |
| Cranelift birth | `70.backend/backend/cranelift_codegen_adapter.spl`, `Aggregate` arm | Region owner installation before `cranelift_store`; array runtime ownership parity |
| Cranelift alias/pointer | Same file, `SetField` and `Store` arms | Untag actual struct identity; typed slot operation replaces raw store |
| MIR interpreter | `95.interp/mir_interpreter.spl`, `Store/Aggregate/SetField`, `_store_const_aggregate`, `_store_string` | Associate actual interpreter storage identity; propagate allocation owner across retained aliases |
| Hosted interpreter | `10.frontend/core/interpreter/_EvalOps/access_literal_assign_eval.spl::eval_assign_expr`, compound assignment, literal constructors; corresponding statement handlers | Barrier inside actual `val_struct_set_field_idx`, `val_struct_upsert_field`, `val_array_set` owners; snapshot copy is a new birth |
| Native machine ISel | `70.backend/backend/native/isel_{x86_64,aarch64,riscv32,riscv64}.spl` | Independent field/pointer/aggregate lowering; unavailable until classified |
| GPU/hardware | CUDA, OpenCL and VHDL backend store dispatch | Reject SOURCE admission; existing device lifetime semantics do not certify this invocation region |
| Containers/text | Runtime calls including array push/set, dictionary insertion/removal, mutable bytes and reallocation | Provider owner parity, immediate typed-edge checks, preserve/retire owner before replacement publication |
| Copy/call/escape | Copy/Move, aggregate materialization, direct/indirect calls, FFI and callbacks | Reference copies preserve identity; value copies allocate in region; unknown effects/foreign mutation fail closed |
| Cached objects | Existing driver native cache/environment identity | Instrumentation ABI must invalidate old artifacts before linking; a backend flag alone is insufficient |

## Shared account bridge dependency

The account authority is `00.common/loop_resource_account_v1.spl::reserve`.
The provider owner reported no sealed native reservation bridge, bounded registry
growth/probe protocol or common container owner on 2026-10-25. Caller-supplied
fuel cannot substitute for this account. A possible split sequence must reserve
the actual provider-certified preparation bound in Simple, then consume the
same one-use prepared operation without intervening callback or mutable lookup
state. Exact descriptor layout, preparation invalidation and operation ABI need
provider/Astra approval before emission.

The final provider/Astra ABI subsequently froze six u64 header words:
`[1, shape, extent, slot_count, table_address, 1]`, and four-u64 slot rows:
`[offset, actual_storage_width, edge_kind, representation]`. Kinds are 1 scalar,
2 same-region mutable, 3 certified immutable; representations are 0 scalar,
1 untagged pointer, 2 tagged pointer. Earlier word-width-header/kinds-0/1/2
sketches are superseded. The implemented private LLVM descriptor emitter uses
this final schema and validates native-word extents and representations.
It is not yet connected to actual constructor emission: producer-owned hidden
context provenance/account forwarding remains a required dependency.

Cranelift's exposed data bridge currently supports readonly string bytes or
scalar globals; neither exposes the required readonly aggregate relocation.
Proposed minimal bridge is `rt_cranelift_declare_readonly_words_v1(module,
name_ptr, name_len, words_ptr, word_count, alignment, reloc_word_index,
reloc_target_data_id, reloc_addend) -> data_id`. A -1 relocation index means
none; otherwise one pointer relocation targets the declared data ID at the
selected word. Emit slots first without relocation, then header with word 4
relocating to slots. This remains a proposal, not an implemented API. Validation
must cover readonly object bytes, exact data relocation, link/run descriptor
reading, and rejection of invalid index/alignment/target without publication.

## First executable acceptance

Parse/lower real `fn subject() -> i64:\n    1\n`; unchanged query reports
NoManifest with zero body visits. Retain the actual function-symbol alias before
inspection, mutate `alias.name`, and require Stale. This requires the complete
allocation/write closure of that fixture, not a SetField-only exemption.
Then exercise descendant array/variant/text writes, pre-query aliases,
same-value stores, replacement followed by legitimate writer, foreign and
preexisting children, copy versus alias, capacity cancellation, epoch overflow,
read/write conflict and close/reuse. Sabotage the real field barrier and demand
the nested-write controls fail. Native and interpreter evidence is independent.
No heavy checks were started because the canonical build owner retains its
resource lease. No runtime or compiler execution PASS is claimed.

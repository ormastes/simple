//! Low Coverage Type Tests Part 2
//! Tests for MIR, dependency tracker, and settlement types
#![allow(unused_imports)]

use std::collections::HashSet;

// =============================================================================
// MIR Instructions Coverage (compiler/src/mir/instructions.rs - 0%)
// =============================================================================

use simple_compiler::mir::{BlockId, VReg};

#[test]
fn test_block_id_creation() {
    let block = BlockId(0);
    assert_eq!(block.0, 0);

    let block2 = BlockId(42);
    assert_eq!(block2.0, 42);
}

#[test]
fn test_block_id_equality() {
    let b1 = BlockId(1);
    let b2 = BlockId(1);
    let b3 = BlockId(2);

    assert_eq!(b1, b2);
    assert_ne!(b1, b3);
}

#[test]
fn test_block_id_hash() {
    use std::collections::HashMap;

    let mut map = HashMap::new();
    map.insert(BlockId(0), "entry");
    map.insert(BlockId(1), "then");
    map.insert(BlockId(2), "else");

    assert_eq!(map.get(&BlockId(0)), Some(&"entry"));
    assert_eq!(map.get(&BlockId(1)), Some(&"then"));
}

#[test]
fn test_vreg_creation() {
    let reg = VReg(0);
    assert_eq!(reg.0, 0);

    let reg2 = VReg(100);
    assert_eq!(reg2.0, 100);
}

#[test]
fn test_vreg_equality() {
    let r1 = VReg(5);
    let r2 = VReg(5);
    let r3 = VReg(10);

    assert_eq!(r1, r2);
    assert_ne!(r1, r3);
}

#[test]
fn test_vreg_hash() {
    use std::collections::HashSet;

    let mut set = HashSet::new();
    set.insert(VReg(0));
    set.insert(VReg(1));
    set.insert(VReg(0)); // duplicate

    assert_eq!(set.len(), 2);
}

// =============================================================================
// MIR Blocks Coverage (compiler/src/mir/blocks.rs - ~46%)
// =============================================================================

use simple_compiler::mir::{BlockBuildState, BlockBuilder, Terminator};

#[test]
fn test_terminator_return_none() {
    let term = Terminator::Return(None);
    assert!(term.is_sealed());
    assert!(!term.is_branching());
    assert!(term.uses().is_empty());
    assert!(term.successors().is_empty());
}

#[test]
fn test_terminator_return_value() {
    let term = Terminator::Return(Some(VReg(0)));
    assert!(term.is_sealed());
    assert!(!term.is_branching());
    assert_eq!(term.uses(), vec![VReg(0)]);
    assert!(term.successors().is_empty());
}

#[test]
fn test_terminator_jump() {
    let term = Terminator::Jump(BlockId(1));
    assert!(term.is_sealed());
    assert!(term.is_branching());
    assert!(term.uses().is_empty());
    assert_eq!(term.successors(), vec![BlockId(1)]);
}

#[test]
fn test_terminator_branch() {
    let term = Terminator::Branch {
        cond: VReg(5),
        then_block: BlockId(1),
        else_block: BlockId(2),
    };
    assert!(term.is_sealed());
    assert!(term.is_branching());
    assert_eq!(term.uses(), vec![VReg(5)]);
    assert_eq!(term.successors(), vec![BlockId(1), BlockId(2)]);
}

#[test]
fn test_terminator_unreachable() {
    let term = Terminator::Unreachable;
    assert!(!term.is_sealed()); // Unreachable is not a real terminator
    assert!(!term.is_branching());
    assert!(term.uses().is_empty());
    assert!(term.successors().is_empty());
}

#[test]
fn test_block_build_state_open() {
    let state = BlockBuildState::Open {
        id: BlockId(0),
        instructions: vec![],
    };
    assert!(matches!(state, BlockBuildState::Open { .. }));
}

#[test]
fn test_block_build_state_sealed() {
    let state = BlockBuildState::Sealed {
        id: BlockId(0),
        instructions: vec![],
        terminator: Terminator::Unreachable,
    };
    assert!(matches!(state, BlockBuildState::Sealed { .. }));
}

#[test]
fn test_block_builder_new() {
    let builder = BlockBuilder::new(BlockId(0));
    assert!(builder.is_open());
    assert!(!builder.is_sealed());
    assert_eq!(builder.id(), BlockId(0));
}

#[test]
fn test_block_builder_seal() {
    let mut builder = BlockBuilder::new(BlockId(0));
    assert!(builder.is_open());

    builder.seal(Terminator::Return(None));
    assert!(builder.is_sealed());
    assert!(!builder.is_open());
}

#[test]
fn test_block_builder_finalize() {
    let mut builder = BlockBuilder::new(BlockId(0));
    builder.seal(Terminator::Return(None));

    let block = builder.finalize();
    assert!(block.is_ok());
}

// =============================================================================
// MIR Effects Coverage (compiler/src/mir/effects.rs - ~40%)
// =============================================================================

use simple_compiler::mir::{CallTarget, Effect, EffectSet};

#[test]
fn test_effect_variants() {
    let _ = Effect::Compute;
    let _ = Effect::Io;
    let _ = Effect::Wait;
    let _ = Effect::GcAlloc;
    let _ = Effect::Net;
    let _ = Effect::Fs;
    let _ = Effect::Unsafe;
}

#[test]
fn test_effect_is_async() {
    assert!(Effect::Compute.is_async());
    assert!(Effect::Io.is_async());
    assert!(!Effect::Wait.is_async());
}

#[test]
fn test_effect_is_nogc() {
    assert!(Effect::Compute.is_nogc());
    assert!(!Effect::GcAlloc.is_nogc());
}

#[test]
fn test_effect_is_pure() {
    assert!(Effect::Compute.is_pure());
    assert!(!Effect::Io.is_pure());
}

#[test]
fn test_effect_is_net() {
    assert!(Effect::Net.is_net());
    assert!(!Effect::Compute.is_net());
}

#[test]
fn test_effect_is_fs() {
    assert!(Effect::Fs.is_fs());
    assert!(!Effect::Compute.is_fs());
}

#[test]
fn test_effect_set_new() {
    let set = EffectSet::new();
    assert!(set.is_pipeline_safe());
    assert!(set.is_nogc());
}

#[test]
fn test_effect_set_push() {
    let mut set = EffectSet::new();
    set.push(Effect::Compute);
    assert!(set.is_pipeline_safe());
}

#[test]
fn test_effect_set_append() {
    let mut set1 = EffectSet::new();
    set1.push(Effect::Compute);

    let mut set2 = EffectSet::new();
    set2.push(Effect::Io);

    set1.append(&set2);
    assert!(set1.is_pipeline_safe());
}

#[test]
fn test_call_target_pure() {
    let target = CallTarget::Pure("my_func".to_string());
    assert!(matches!(target, CallTarget::Pure(_)));
}

#[test]
fn test_call_target_io() {
    let target = CallTarget::Io("io_func".to_string());
    assert!(matches!(target, CallTarget::Io(_)));
}

#[test]
fn test_call_target_blocking() {
    let target = CallTarget::Blocking("blocking_fn".to_string());
    assert!(matches!(target, CallTarget::Blocking(_)));
}

#[test]
fn test_call_target_gc_allocating() {
    let target = CallTarget::GcAllocating("alloc_fn".to_string());
    assert!(matches!(target, CallTarget::GcAllocating(_)));
}

#[test]
fn test_call_target_net() {
    let target = CallTarget::Net("net_fn".to_string());
    assert!(matches!(target, CallTarget::Net(_)));
}

#[test]
fn test_call_target_fs() {
    let target = CallTarget::Fs("fs_fn".to_string());
    assert!(matches!(target, CallTarget::Fs(_)));
}

#[test]
fn test_call_target_unsafe() {
    let target = CallTarget::Unsafe("unsafe_fn".to_string());
    assert!(matches!(target, CallTarget::Unsafe(_)));
}

// =============================================================================
// Settlement Types Coverage (loader/src/settlement/container.rs - 0%)
// =============================================================================

use simple_loader::settlement::{ModuleHandle, SettlementError};

#[test]
fn test_module_handle_creation() {
    let handle = ModuleHandle(0);
    assert_eq!(handle.0, 0);
    assert!(handle.is_valid());
}

#[test]
fn test_module_handle_invalid() {
    let handle = ModuleHandle::INVALID;
    assert!(!handle.is_valid());
}

#[test]
fn test_module_handle_as_usize() {
    let handle = ModuleHandle(42);
    assert_eq!(handle.as_usize(), 42);
}

#[test]
fn test_settlement_error_display() {
    let err = SettlementError::CodeRegionFull;
    let msg = format!("{}", err);
    assert!(!msg.is_empty());

    let err2 = SettlementError::ModuleNotFound("test".to_string());
    let msg2 = format!("{}", err2);
    assert!(msg2.contains("test"));

    let err3 = SettlementError::HasDependents("main".to_string(), vec!["dep1".to_string()]);
    let msg3 = format!("{}", err3);
    assert!(msg3.contains("main"));
}

#[test]
fn test_settlement_error_variants() {
    let _ = SettlementError::CodeRegionFull;
    let _ = SettlementError::DataRegionFull;
    let _ = SettlementError::ModuleNotFound("x".to_string());
    let _ = SettlementError::HasDependents("x".to_string(), vec![]);
    let _ = SettlementError::NativeLibError("x".to_string());
    let _ = SettlementError::MemoryError("x".to_string());
    let _ = SettlementError::InvalidModule("x".to_string());
    let _ = SettlementError::DependencyCycle(vec![]);
}

// =============================================================================
// Settlement Slots Coverage (loader/src/settlement/slots.rs - 0%)
// =============================================================================

use simple_loader::settlement::{SlotAllocator, SlotRange, CODE_SLOT_SIZE, DATA_SLOT_SIZE};

#[test]
fn test_slot_range_creation() {
    let range = SlotRange::new(0, 10);
    assert_eq!(range.start, 0);
    assert_eq!(range.count, 10);
}

#[test]
fn test_slot_range_end() {
    let range = SlotRange::new(5, 10);
    assert_eq!(range.end(), 15);
}

#[test]
fn test_slot_range_contains() {
    let range = SlotRange::new(5, 10);
    assert!(range.contains(5));
    assert!(range.contains(10));
    assert!(!range.contains(15));
    assert!(!range.contains(4));
}

#[test]
fn test_slot_allocator_new() {
    // Create a small buffer for testing
    let mut buffer = vec![0u8; CODE_SLOT_SIZE * 10];
    let allocator = SlotAllocator::new(buffer.as_mut_ptr(), buffer.len(), CODE_SLOT_SIZE);
    assert_eq!(allocator.total_slots(), 10);
    assert_eq!(allocator.free_slots(), 10);
    assert_eq!(allocator.used_slots(), 0);
}

#[test]
fn test_slot_allocator_allocate() {
    let mut buffer = vec![0u8; CODE_SLOT_SIZE * 100];
    let mut allocator = SlotAllocator::new(buffer.as_mut_ptr(), buffer.len(), CODE_SLOT_SIZE);

    let range = allocator.allocate(10);
    assert!(range.is_some());
    assert_eq!(allocator.used_slots(), 10);
    assert_eq!(allocator.free_slots(), 90);
}

#[test]
fn test_slot_allocator_allocate_full() {
    let mut buffer = vec![0u8; CODE_SLOT_SIZE * 10];
    let mut allocator = SlotAllocator::new(buffer.as_mut_ptr(), buffer.len(), CODE_SLOT_SIZE);

    let range = allocator.allocate(15);
    assert!(range.is_none()); // Not enough space
}

#[test]
fn test_slot_size_constants() {
    // Verify the constants are reasonable
    assert!(CODE_SLOT_SIZE > 0);
    assert!(DATA_SLOT_SIZE > 0);
}

// =============================================================================
// Settlement Tables Coverage (loader/src/settlement/tables.rs - 0%)
// =============================================================================

use simple_loader::settlement::{FunctionTable, GlobalTable, TableIndex, TypeTable};

#[test]
fn test_table_index() {
    let idx = TableIndex(0);
    assert_eq!(idx.0, 0);
}

#[test]
fn test_function_table_new() {
    let table = FunctionTable::new();
    assert_eq!(table.len(), 0);
}

#[test]
fn test_function_table_with_capacity() {
    let table = FunctionTable::with_capacity(100);
    assert_eq!(table.len(), 0);
}

#[test]
fn test_global_table_new() {
    let table = GlobalTable::new();
    assert_eq!(table.len(), 0);
}

#[test]
fn test_global_table_with_capacity() {
    let table = GlobalTable::with_capacity(50);
    assert_eq!(table.len(), 0);
}

#[test]
fn test_type_table_new() {
    let table = TypeTable::new();
    assert_eq!(table.len(), 0);
}

#[test]
fn test_type_table_with_capacity() {
    let table = TypeTable::with_capacity(200);
    assert_eq!(table.len(), 0);
}

// =============================================================================
// Dependency Tracker - ImportGraph Coverage (dependency_tracker/src/graph.rs - 0%)
// =============================================================================
// Dependency Tracker - MacroImport Coverage (dependency_tracker/src/macro_import.rs - 0%)
// =============================================================================
// Dependency Tracker - Symbol Coverage (dependency_tracker/src/symbol.rs - 0%)
// =============================================================================
// HIR Types Coverage (compiler/src/hir/types.rs - ~10%)
// =============================================================================

use simple_compiler::hir::{HirType, Signedness, TypeId, TypeRegistry};

#[test]
fn test_type_id_creation() {
    let id = TypeId(0);
    assert_eq!(id.0, 0);
}

#[test]
fn test_signedness() {
    let signed = Signedness::Signed;
    let unsigned = Signedness::Unsigned;

    assert!(matches!(signed, Signedness::Signed));
    assert!(matches!(unsigned, Signedness::Unsigned));
}

#[test]
fn test_hir_type_int() {
    let ty = HirType::Int {
        bits: 64,
        signedness: Signedness::Signed,
    };
    assert!(matches!(ty, HirType::Int { bits: 64, .. }));
}

#[test]
fn test_hir_type_float() {
    let ty = HirType::Float { bits: 64 };
    assert!(matches!(ty, HirType::Float { bits: 64 }));
}

#[test]
fn test_hir_type_bool() {
    let ty = HirType::Bool;
    assert!(matches!(ty, HirType::Bool));
}

#[test]
fn test_hir_type_string() {
    let ty = HirType::String;
    assert!(matches!(ty, HirType::String));
}

#[test]
fn test_hir_type_nil() {
    let ty = HirType::Nil;
    assert!(matches!(ty, HirType::Nil));
}

#[test]
fn test_type_registry_new() {
    let registry = TypeRegistry::new();
    let _ = registry;
}

#[test]
fn test_type_registry_register() {
    let mut registry = TypeRegistry::new();
    let id = registry.register(HirType::Bool);
    assert!(id.0 >= 0);
}

#[test]
fn test_type_registry_register_named() {
    let mut registry = TypeRegistry::new();
    let id = registry.register_named("MyType".to_string(), HirType::Bool);
    assert!(id.0 >= 0);

    let looked_up = registry.lookup("MyType");
    assert!(looked_up.is_some());
}

#[test]
fn test_type_registry_get() {
    let mut registry = TypeRegistry::new();
    let id = registry.register(HirType::String);

    let ty = registry.get(id);
    assert!(ty.is_some());
    assert!(matches!(ty.unwrap(), HirType::String));
}

// =============================================================================
// AsyncEffect Coverage (compiler/src/mir/effects.rs)
// =============================================================================

use simple_compiler::mir::{is_async, nogc, pipeline_safe, AsyncEffect, NogcInstr};

#[test]
fn test_async_effect_variants() {
    let _ = AsyncEffect::Compute;
    let _ = AsyncEffect::Io;
    let _ = AsyncEffect::Wait;
}

#[test]
fn test_is_async_function() {
    assert!(is_async(AsyncEffect::Compute));
    assert!(is_async(AsyncEffect::Io));
    assert!(!is_async(AsyncEffect::Wait));
}

#[test]
fn test_pipeline_safe_function() {
    assert!(pipeline_safe(&[AsyncEffect::Compute, AsyncEffect::Io]));
    assert!(!pipeline_safe(&[AsyncEffect::Wait]));
    assert!(!pipeline_safe(&[AsyncEffect::Compute, AsyncEffect::Wait]));
}

#[test]
fn test_nogc_instr_variants() {
    let _ = NogcInstr::Const(42);
    let _ = NogcInstr::Add;
    let _ = NogcInstr::GcAlloc;
}

#[test]
fn test_nogc_function() {
    assert!(nogc(&[NogcInstr::Const(1), NogcInstr::Add]));
    assert!(!nogc(&[NogcInstr::GcAlloc]));
}

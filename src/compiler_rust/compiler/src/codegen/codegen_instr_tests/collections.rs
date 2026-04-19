use super::aot_compiles;
use crate::hir::TypeId;
use crate::mir::{BlockId, FStringPart, MirInst};

// =============================================================================
// Collections — ArrayLit, TupleLit, DictLit (collections.rs)
// =============================================================================

#[test]
fn codegen_array_lit() {
    assert!(aot_compiles("array_lit", |f| {
        let a = f.new_vreg();
        let b = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
        block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
        block.instructions.push(MirInst::ArrayLit {
            dest,
            elements: vec![a, b],
        });
        dest
    }));
}

#[test]
fn codegen_tuple_lit() {
    assert!(aot_compiles("tuple_lit", |f| {
        let a = f.new_vreg();
        let b = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
        block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
        block.instructions.push(MirInst::TupleLit {
            dest,
            elements: vec![a, b],
        });
        dest
    }));
}

#[test]
fn codegen_dict_lit() {
    assert!(aot_compiles("dict_lit", |f| {
        let k = f.new_vreg();
        let v = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: k, value: 1 });
        block.instructions.push(MirInst::ConstInt { dest: v, value: 42 });
        block.instructions.push(MirInst::DictLit {
            dest,
            keys: vec![k],
            values: vec![v],
        });
        dest
    }));
}

#[test]
fn codegen_vec_lit() {
    assert!(aot_compiles("vec_lit", |f| {
        let a = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
        block.instructions.push(MirInst::VecLit {
            dest,
            elements: vec![a],
        });
        dest
    }));
}

// =============================================================================
// IndexGet / IndexSet / SliceOp (collections.rs)
// =============================================================================

#[test]
fn codegen_index_get() {
    assert!(aot_compiles("idx_get", |f| {
        let a = f.new_vreg();
        let arr = f.new_vreg();
        let idx = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 42 });
        block.instructions.push(MirInst::ArrayLit {
            dest: arr,
            elements: vec![a],
        });
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::IndexGet {
            dest,
            collection: arr,
            index: idx,
        });
        dest
    }));
}

#[test]
fn codegen_index_set() {
    assert!(aot_compiles("idx_set", |f| {
        let a = f.new_vreg();
        let arr = f.new_vreg();
        let idx = f.new_vreg();
        let val = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 0 });
        block.instructions.push(MirInst::ArrayLit {
            dest: arr,
            elements: vec![a],
        });
        block.instructions.push(MirInst::ConstInt { dest: idx, value: 0 });
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::IndexSet {
            collection: arr,
            index: idx,
            value: val,
        });
        arr
    }));
}

#[test]
fn codegen_slice_op() {
    assert!(aot_compiles("slice_op", |f| {
        let a = f.new_vreg();
        let b = f.new_vreg();
        let arr = f.new_vreg();
        let start = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: a, value: 1 });
        block.instructions.push(MirInst::ConstInt { dest: b, value: 2 });
        block.instructions.push(MirInst::ArrayLit {
            dest: arr,
            elements: vec![a, b],
        });
        block.instructions.push(MirInst::ConstInt { dest: start, value: 0 });
        block.instructions.push(MirInst::SliceOp {
            dest,
            collection: arr,
            start: Some(start),
            end: None,
            step: None,
        });
        dest
    }));
}

// =============================================================================
// String / FString (collections.rs)
// =============================================================================

#[test]
fn codegen_const_string() {
    assert!(aot_compiles("const_str", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstString {
                dest,
                value: "hello".to_string(),
            });
        dest
    }));
}

#[test]
fn codegen_const_symbol() {
    assert!(aot_compiles("const_sym", |f| {
        let dest = f.new_vreg();
        f.block_mut(BlockId(0))
            .unwrap()
            .instructions
            .push(MirInst::ConstSymbol {
                dest,
                value: "my_sym".to_string(),
            });
        dest
    }));
}

#[test]
fn codegen_fstring_format() {
    assert!(aot_compiles("fstr", |f| {
        let val = f.new_vreg();
        let boxed = f.new_vreg();
        let dest = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::BoxInt {
            dest: boxed,
            value: val,
        });
        block.instructions.push(MirInst::FStringFormat {
            dest,
            parts: vec![FStringPart::Literal("value=".to_string()), FStringPart::Expr(boxed)],
        });
        dest
    }));
}

// =============================================================================
// Struct / Field (closures_structs.rs, fields.rs)
// =============================================================================

#[test]
fn codegen_struct_init_field_get_set() {
    assert!(aot_compiles("struct_ops", |f| {
        let val = f.new_vreg();
        let obj = f.new_vreg();
        let got = f.new_vreg();
        let newval = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: val, value: 42 });
        block.instructions.push(MirInst::StructInit {
            dest: obj,
            type_id: TypeId::I64,
            struct_size: 8,
            field_offsets: vec![0],
            field_types: vec![TypeId::I64],
            field_values: vec![val],
        });
        block.instructions.push(MirInst::FieldGet {
            dest: got,
            object: obj,
            byte_offset: 0,
            field_type: TypeId::I64,
        });
        block.instructions.push(MirInst::ConstInt {
            dest: newval,
            value: 99,
        });
        block.instructions.push(MirInst::FieldSet {
            object: obj,
            byte_offset: 0,
            field_type: TypeId::I64,
            value: newval,
        });
        got
    }));
}

#[test]
fn codegen_struct_field_get_native_types() {
    assert!(aot_compiles("struct_native_fields", |f| {
        let int_val = f.new_vreg();
        let float_val = f.new_vreg();
        let obj = f.new_vreg();
        let got_int = f.new_vreg();
        let got_float = f.new_vreg();
        let block = f.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::ConstInt { dest: int_val, value: 42 });
        block.instructions.push(MirInst::ConstFloat { dest: float_val, value: 3.5 });
        block.instructions.push(MirInst::StructInit {
            dest: obj,
            type_id: TypeId::I64,
            struct_size: 16,
            field_offsets: vec![0, 8],
            field_types: vec![TypeId::I32, TypeId::F64],
            field_values: vec![int_val, float_val],
        });
        block.instructions.push(MirInst::FieldGet {
            dest: got_int,
            object: obj,
            byte_offset: 0,
            field_type: TypeId::I32,
        });
        block.instructions.push(MirInst::FieldGet {
            dest: got_float,
            object: obj,
            byte_offset: 8,
            field_type: TypeId::F64,
        });
        got_int
    }));
}

//! The C-string return census must stay reachable through registered-runtime
//! call lowering; generic external calls do not perform this ABI conversion.
use super::aot_object;
use crate::codegen::instr::calls::C_STRING_RETURNING_RUNTIME_FNS;
use crate::codegen::runtime_sffi::spec_for;
use crate::mir::{BlockId, CallTarget, MirInst};
use cranelift_codegen::ir::types;
use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

fn relocation_count(bytes: &[u8], name: &str) -> usize {
    let file = object::File::parse(bytes).expect("native object");
    file.sections()
        .map(|section| {
            section.relocations().filter(|(_, relocation)| {
                let RelocationTarget::Symbol(index) = relocation.target() else {
                    return false;
                };
                let symbol = file.symbol_by_index(index).expect("relocation symbol");
                let actual = symbol.name().expect("symbol name");
                if actual != name && actual.strip_prefix('_') != Some(name) {
                    return false;
                }
                // Mach-O ARM64 uses a GOT page/load relocation pair for one
                // call. Count its high half once, or a direct branch once.
                if file.architecture() == object::Architecture::Aarch64
                    && file.format() == object::BinaryFormat::MachO
                {
                    let object::RelocationFlags::MachO { r_type, .. } = relocation.flags() else {
                        panic!("unexpected ARM64 Mach-O relocation: {relocation:?}");
                    };
                    return match r_type {
                        object::macho::ARM64_RELOC_BRANCH26
                        | object::macho::ARM64_RELOC_PAGE21
                        | object::macho::ARM64_RELOC_GOT_LOAD_PAGE21 => true,
                        object::macho::ARM64_RELOC_PAGEOFF12
                        | object::macho::ARM64_RELOC_GOT_LOAD_PAGEOFF12 => false,
                        _ => panic!("unexpected call relocation for {name}: {relocation:?}"),
                    };
                }
                true
            }).count()
        })
        .sum()
}

fn call_object(name: &str, arity: usize, consumed: bool) -> Vec<u8> {
    aot_object("cstring_return_probe", |function| {
        let mut args = Vec::new();
        for _ in 0..arity {
            let arg = function.new_vreg();
            function.block_mut(BlockId(0)).unwrap().instructions.push(
                MirInst::ConstInt { dest: arg, value: 7 });
            args.push(arg);
        }
        let dest = function.new_vreg();
        let block = function.block_mut(BlockId(0)).unwrap();
        block.instructions.push(MirInst::Call {
            dest: consumed.then_some(dest),
            target: CallTarget::from_name(name),
            args,
        });
        if !consumed {
            block.instructions.push(MirInst::ConstInt { dest, value: 0 });
        }
        dest
    })
}

#[test]
fn cstring_returns_registry_has_every_exact_signature() {
    assert_eq!(C_STRING_RETURNING_RUNTIME_FNS, &[
        "rt_cuda_device_name", "rt_cuda_get_error_string", "rt_metal_device_name",
        "rt_metal_get_last_error", "rt_vulkan_device_driver_identity",
        "rt_vulkan_device_name", "rt_vulkan_device_type", "rt_vulkan_get_last_error",
        "rt_vulkan_selected_device_driver_identity", "rt_vulkan_selected_device_name",
        "rt_vulkan_selected_device_type",
    ]);
    for &name in C_STRING_RETURNING_RUNTIME_FNS {
        let spec = spec_for(name).unwrap_or_else(|| panic!("missing C-string runtime signature: {name}"));
        let arity = match name {
            "rt_cuda_device_name" | "rt_cuda_get_error_string" | "rt_metal_device_name"
            | "rt_vulkan_device_driver_identity" | "rt_vulkan_device_name"
            | "rt_vulkan_device_type" => 1,
            "rt_metal_get_last_error" | "rt_vulkan_get_last_error"
            | "rt_vulkan_selected_device_driver_identity" | "rt_vulkan_selected_device_name"
            | "rt_vulkan_selected_device_type" => 0,
            _ => panic!("add exact signature expectation for {name}"),
        };
        assert_eq!(spec.params, vec![types::I64; arity], "{name}");
        assert_eq!(spec.returns, &[types::I64], "{name}");
    }
}

#[test]
fn cstring_returns_native_calls_decode_each_gpu_result_exactly_once() {
    for &name in C_STRING_RETURNING_RUNTIME_FNS {
        // Derive arity independently of the registry so a missing entry reaches
        // actual native lowering and fails on its absent conversion relocation.
        let arity = usize::from(matches!(name,
            "rt_cuda_device_name" | "rt_cuda_get_error_string" | "rt_metal_device_name"
            | "rt_vulkan_device_driver_identity" | "rt_vulkan_device_name"
            | "rt_vulkan_device_type"));
        let object = call_object(name, arity, true);
        assert_eq!(relocation_count(&object, name), 1, "{name}");
        assert_eq!(relocation_count(&object, "rt_cstring_to_text"), 1, "{name}");
    }
}

#[test]
fn cstring_returns_native_does_not_decode_boxed_text_or_scalar_results() {
    for (name, arity) in [("rt_env_cwd", 0), ("rt_vulkan_selected_device_driver_identity_hash", 0)] {
        let object = call_object(name, arity, true);
        assert_eq!(relocation_count(&object, name), 1, "{name}");
        assert_eq!(relocation_count(&object, "rt_cstring_to_text"), 0, "{name}");
    }
}

#[test]
fn cstring_returns_native_discarded_result_does_not_allocate_text() {
    let object = call_object("rt_vulkan_get_last_error", 0, false);
    assert_eq!(relocation_count(&object, "rt_vulkan_get_last_error"), 1);
    assert_eq!(relocation_count(&object, "rt_cstring_to_text"), 0);
}

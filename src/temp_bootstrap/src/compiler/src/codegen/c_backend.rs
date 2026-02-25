//! C code generation backend.
//!
//! Translates a `MirModule` into a complete C source file that can be compiled
//! with clang/gcc. The generated C links against the Simple runtime (`runtime.h`).

use std::collections::HashMap;

use crate::error::CompileError;
use crate::mir::{MirInst, MirModule};
use crate::value::FUNC_MAIN;

use super::c_instr::{compile_instruction, compile_terminator, sanitize_name, CInstrContext};
use super::c_runtime_ffi::generate_runtime_declarations;
use super::c_types::{type_id_to_c_param, type_id_to_c_return};

/// C code generation backend.
///
/// Unlike `NativeBackend` (which returns `Vec<u8>` object code), this returns
/// a `String` of C source text.
#[derive(Default)]
pub struct CCodegen {
    /// Accumulated C source output.
    output: String,
}

impl CCodegen {
    pub fn new() -> Self {
        Self::default()
    }

    /// Compile a MIR module to a complete C source file.
    pub fn compile_module(&mut self, mir: &MirModule) -> Result<String, CompileError> {
        self.output.clear();

        // 1. Preamble: includes and runtime declarations
        self.emit_preamble();

        // 1b. Collect all lambda names referenced by ClosureCreate instructions.
        //     These lambdas are not emitted as separate MirFunctions, so we emit
        //     a single generic stub and forward-declare each lambda name as an alias.
        let lambda_names = collect_lambda_names(mir);
        if !lambda_names.is_empty() {
            self.output
                .push_str("/* Bootstrap lambda stub (lambdas not executed in bootstrap) */\n");
            self.output
                .push_str("static int64_t __bootstrap_lambda_stub(void) { return 0; }\n");
            for lname in &lambda_names {
                // Emit a #define so that &lambda_name resolves to &__bootstrap_lambda_stub
                self.output.push_str(&format!(
                    "#define {} __bootstrap_lambda_stub\n",
                    lname
                ));
            }
            self.output.push('\n');
        }

        // 2. Compile all functions, collecting string constants.
        //    Track emitted function names to deduplicate (Issue 2: redefinition errors).
        let mut all_string_constants: Vec<(String, String)> = Vec::new();
        let mut function_bodies: Vec<String> = Vec::new();
        let mut forward_decls: Vec<String> = Vec::new();
        let mut name_counts: HashMap<String, usize> = HashMap::new();

        for func in &mir.functions {
            // Forward declaration
            let ret_type = type_id_to_c_return(func.return_type);
            // Rename "main" to "simple_main" to avoid conflict with C entry point
            let base_name = if func.name == FUNC_MAIN {
                "simple_main".to_string()
            } else {
                sanitize_name(&func.name)
            };

            // Deduplicate: if this name was already emitted, append _N suffix
            let count = name_counts.entry(base_name.clone()).or_insert(0);
            let name = if *count == 0 {
                base_name.clone()
            } else {
                format!("{}_{}", base_name, count)
            };
            *name_counts.get_mut(&base_name).unwrap() += 1;

            let params: Vec<String> = func
                .params
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    format!("{} _v{}", type_id_to_c_param(p.ty), i)
                })
                .collect();
            let params_str = if params.is_empty() {
                "void".to_string()
            } else {
                params.join(", ")
            };
            forward_decls.push(format!("{} {}({});", ret_type, name, params_str));

            // Function body
            let mut ctx = CInstrContext::new();
            // Carry forward the string counter from previous functions
            ctx.string_counter = all_string_constants.len();

            let mut body = String::new();
            body.push_str(&format!("{} {}({}) {{\n", ret_type, name, params_str));

            // Declare local variables (all params + locals as int64_t by default)
            // Params are already declared as function parameters (indices 0..params.len())
            // Collect all vregs used in the function to declare them
            let max_vreg = compute_max_vreg(func);
            let param_count = func.params.len() as u32;
            if max_vreg >= param_count {
                let mut decls: Vec<String> = Vec::new();
                for i in param_count..=max_vreg {
                    decls.push(format!("_v{}", i));
                }
                if !decls.is_empty() {
                    body.push_str(&format!("    int64_t {};\n", decls.join(", ")));
                }
            }

            // Declare _local_N stack slots used by LocalAddr instructions
            let local_indices = collect_local_indices(func);
            for idx in &local_indices {
                body.push_str(&format!("    int64_t _local_{};\n", idx));
            }

            // Emit blocks
            for block in &func.blocks {
                body.push_str(&format!("bb{}:;\n", block.id.0));

                // Instructions
                for inst in &block.instructions {
                    compile_instruction(&mut ctx, inst);
                }

                // Terminator
                compile_terminator(&mut ctx, &block.terminator);

                // Flush accumulated lines
                for line in ctx.lines.drain(..) {
                    body.push_str(&line);
                    body.push('\n');
                }
            }

            body.push_str("}\n\n");
            function_bodies.push(body);

            // Collect string constants from this function
            all_string_constants.extend(ctx.string_constants);
        }

        // 3. Emit string constants
        if !all_string_constants.is_empty() {
            self.output.push_str("/* String constants */\n");
            for (label, value) in &all_string_constants {
                self.output.push_str(&format!(
                    "static const char {}[] = \"{}\";\n",
                    label,
                    escape_c_string(value)
                ));
            }
            self.output.push('\n');
        }

        // 4. Emit forward declarations
        if !forward_decls.is_empty() {
            self.output.push_str("/* Forward declarations */\n");
            for decl in &forward_decls {
                self.output.push_str(decl);
                self.output.push('\n');
            }
            self.output.push('\n');
        }

        // 5. Emit function bodies
        for body in &function_bodies {
            self.output.push_str(body);
        }

        // 6. Emit main entry point (if simple_main exists)
        let has_main = mir.functions.iter().any(|f| f.name == FUNC_MAIN);
        if has_main {
            self.emit_entry_point();
        }

        Ok(self.output.clone())
    }

    /// Emit the C preamble (includes, typedefs, runtime declarations).
    fn emit_preamble(&mut self) {
        self.output.push_str("/* Generated by Simple C backend */\n");
        self.output.push_str("#include <stdint.h>\n");
        self.output.push_str("#include <stdlib.h>\n");
        self.output.push_str("#include <string.h>\n");
        self.output.push_str("#include <math.h>\n");
        self.output.push('\n');

        // Runtime FFI declarations
        self.output.push_str(&generate_runtime_declarations());
        self.output.push('\n');
    }

    /// Emit the C `main` entry point that calls `simple_main`.
    fn emit_entry_point(&mut self) {
        self.output.push_str("/* Entry point */\n");
        self.output
            .push_str("int main(int argc, char** argv) {\n");
        self.output
            .push_str("    return (int)simple_main();\n");
        self.output.push_str("}\n");
    }
}

/// Collect all unique local_index values referenced by LocalAddr instructions.
fn collect_local_indices(func: &crate::mir::MirFunction) -> Vec<usize> {
    use std::collections::BTreeSet;
    let mut indices = BTreeSet::new();
    for block in &func.blocks {
        for inst in &block.instructions {
            if let crate::mir::MirInst::LocalAddr { local_index, .. } = inst {
                indices.insert(*local_index);
            }
        }
    }
    indices.into_iter().collect()
}

/// Compute the maximum VReg index used in a function.
fn compute_max_vreg(func: &crate::mir::MirFunction) -> u32 {
    let mut max = 0u32;
    // Include params
    if !func.params.is_empty() {
        max = (func.params.len() as u32).saturating_sub(1);
    }
    for block in &func.blocks {
        for inst in &block.instructions {
            if let Some(d) = inst.dest() {
                max = max.max(d.0);
            }
            for u in inst.uses() {
                max = max.max(u.0);
            }
        }
        for u in block.terminator.uses() {
            max = max.max(u.0);
        }
    }
    max
}

/// Escape a string for C string literal.
fn escape_c_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c.is_ascii_graphic() || c == ' ' => out.push(c),
            c => {
                // Unicode escape as octal sequences
                let mut buf = [0u8; 4];
                let encoded = c.encode_utf8(&mut buf);
                for b in encoded.bytes() {
                    out.push_str(&format!("\\x{:02x}", b));
                }
            }
        }
    }
    out
}

/// Collect all unique lambda function names referenced by ClosureCreate instructions.
///
/// These lambda functions are referenced in the MIR but not emitted as separate
/// MirFunction entries. We collect their sanitized names so the C backend can
/// emit stubs or #defines to satisfy the linker.
fn collect_lambda_names(mir: &MirModule) -> Vec<String> {
    use std::collections::BTreeSet;
    let mut names = BTreeSet::new();
    // Also collect the set of function names that ARE defined in the module
    let defined: std::collections::HashSet<String> = mir
        .functions
        .iter()
        .map(|f| sanitize_name(&f.name))
        .collect();

    for func in &mir.functions {
        for block in &func.blocks {
            for inst in &block.instructions {
                if let MirInst::ClosureCreate { func_name, .. } = inst {
                    let sname = sanitize_name(func_name);
                    // Only stub lambdas that are NOT already defined as real functions
                    if !defined.contains(&sname) {
                        names.insert(sname);
                    }
                }
            }
        }
    }
    names.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{BinOp, TypeId};
    use crate::mir::{BlockId, MirBlock, MirFunction, MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    /// Helper: create a minimal MIR module with a main function returning 42.
    fn make_return_42_module() -> MirModule {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let r0 = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r0, value: 42 });
        entry.terminator = Terminator::Return(Some(r0));

        let mut module = MirModule::new();
        module.functions.push(func);
        module
    }

    #[test]
    fn test_basic_return_42() {
        let module = make_return_42_module();
        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        // Should contain key pieces
        assert!(result.contains("#include <stdint.h>"));
        assert!(result.contains("int64_t simple_main(void)"));
        assert!(result.contains("_v0 = (int64_t)42;"));
        assert!(result.contains("return _v0;"));
        assert!(result.contains("int main(int argc, char** argv)"));
        assert!(result.contains("simple_main()"));
    }

    #[test]
    fn test_add_two_numbers() {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let r0 = func.new_vreg();
        let r1 = func.new_vreg();
        let r2 = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r0, value: 40 });
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r1, value: 2 });
        entry.instructions.push(MirInst::BinOp {
            dest: r2,
            op: BinOp::Add,
            left: r0,
            right: r1,
        });
        entry.terminator = Terminator::Return(Some(r2));

        let mut module = MirModule::new();
        module.functions.push(func);

        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("_v0 = (int64_t)40;"));
        assert!(result.contains("_v1 = (int64_t)2;"));
        assert!(result.contains("_v2 = _v0 + _v1;"));
        assert!(result.contains("return _v2;"));
    }

    #[test]
    fn test_string_constants() {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let r0 = func.new_vreg();
        let r1 = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstString {
            dest: r0,
            value: "hello".to_string(),
        });
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r1, value: 0 });
        entry.terminator = Terminator::Return(Some(r1));

        let mut module = MirModule::new();
        module.functions.push(func);

        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("static const char _str_0[] = \"hello\";"));
    }

    #[test]
    fn test_escape_c_string() {
        assert_eq!(escape_c_string("hello"), "hello");
        assert_eq!(escape_c_string("he\"llo"), "he\\\"llo");
        assert_eq!(escape_c_string("line\nnext"), "line\\nnext");
        assert_eq!(escape_c_string("tab\there"), "tab\\there");
        assert_eq!(escape_c_string("back\\slash"), "back\\\\slash");
    }

    #[test]
    fn test_branch_codegen() {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let r0 = func.new_vreg(); // condition
        let r1 = func.new_vreg(); // result

        let then_block = func.new_block();
        let else_block = func.new_block();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstBool {
            dest: r0,
            value: true,
        });
        entry.terminator = Terminator::Branch {
            cond: r0,
            then_block,
            else_block,
        };

        func.block_mut(then_block).unwrap().instructions.push(
            MirInst::ConstInt { dest: r1, value: 1 },
        );
        func.block_mut(then_block).unwrap().terminator =
            Terminator::Return(Some(r1));

        func.block_mut(else_block).unwrap().instructions.push(
            MirInst::ConstInt { dest: r1, value: 0 },
        );
        func.block_mut(else_block).unwrap().terminator =
            Terminator::Return(Some(r1));

        let mut module = MirModule::new();
        module.functions.push(func);

        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("if (_v0) goto bb1; else goto bb2;"));
        assert!(result.contains("bb1:;"));
        assert!(result.contains("bb2:;"));
    }

    #[test]
    fn test_no_entry_point_without_main() {
        let func = MirFunction::new("helper".to_string(), TypeId::I64, Visibility::Public);
        let mut module = MirModule::new();
        module.functions.push(func);

        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        // Should NOT have C main entry point since there's no "main" function
        assert!(!result.contains("int main(int argc"));
    }

    #[test]
    fn test_forward_declarations() {
        let module = make_return_42_module();
        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("/* Forward declarations */"));
        assert!(result.contains("int64_t simple_main(void);"));
    }

    #[test]
    fn test_runtime_ffi_declarations() {
        let module = make_return_42_module();
        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("extern int64_t rt_array_new("));
        assert!(result.contains("extern int64_t rt_string_concat("));
    }
}

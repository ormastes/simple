use std::path::{Path, PathBuf};

use super::tools::find_c_compiler;

fn escape_c_asm_string(s: &str) -> String {
    let mut out = String::new();
    for ch in s.chars() {
        match ch {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => {}
            '\t' => out.push_str("\\t"),
            '%' => out.push_str("%%"),
            _ => out.push(ch),
        }
    }
    out
}

fn target_uses_x86_intel_asm(target: Option<(&str, &str, &str)>) -> bool {
    target
        .map(|(triple, _, _)| triple.contains("x86_64") || triple.starts_with("i386"))
        .unwrap_or(false)
}

fn has_unresolved_simple_operand(instruction: &str) -> bool {
    instruction.contains('{') || instruction.contains('}')
}

pub(crate) fn write_inline_asm_c_for_target(
    temp_dir: &Path,
    target: Option<(&str, &str, &str)>,
) -> Result<Option<PathBuf>, String> {
    let blocks = crate::codegen::inline_asm::collected_inline_asm_blocks();
    if blocks.is_empty() {
        return Ok(None);
    }

    let use_intel_syntax = target_uses_x86_intel_asm(target);
    let path = temp_dir.join("simple_asm_blocks.c");
    let mut code = String::from("/* Auto-generated Simple raw asm blocks. */\n\n");
    for block in blocks {
        code.push_str(&format!("__attribute__((used)) void {}(void) {{\n", block.symbol));
        code.push_str("    __asm__ volatile (\n");
        if use_intel_syntax {
            code.push_str("        \".intel_syntax noprefix\\n\"\n");
        }
        for instruction in &block.instructions {
            if has_unresolved_simple_operand(instruction) {
                code.push_str("        \"# skipped Simple asm with unresolved operands\\n\"\n");
            } else {
                code.push_str(&format!("        \"{}\\n\"\n", escape_c_asm_string(instruction)));
            }
        }
        if use_intel_syntax {
            code.push_str("        \".att_syntax prefix\\n\"\n");
        }
        code.push_str("        ::: \"memory\"\n");
        code.push_str("    );\n");
        code.push_str("}\n\n");
    }
    std::fs::write(&path, code).map_err(|e| format!("write inline asm C: {e}"))?;
    Ok(Some(path))
}

pub(crate) fn write_inline_asm_c(temp_dir: &Path) -> Result<Option<PathBuf>, String> {
    write_inline_asm_c_for_target(temp_dir, None)
}

pub(crate) fn compile_inline_asm_c(
    temp_dir: &Path,
    target: Option<(&str, &str, &str)>,
) -> Result<Option<PathBuf>, String> {
    if let Some((triple, _, _)) = target {
        if triple.starts_with("aarch64") || triple.starts_with("arm") {
            if !crate::codegen::inline_asm::collected_inline_asm_blocks().is_empty() {
                return Ok(None);
            }
        }
    }
    let Some(c_path) = write_inline_asm_c_for_target(temp_dir, target)? else {
        return Ok(None);
    };
    let out = temp_dir.join("simple_asm_blocks.o");
    let cc = find_c_compiler();
    let mut cmd = std::process::Command::new(&cc);
    cmd.arg("-c").arg("-o").arg(&out).arg(&c_path);
    if let Some((triple, march, mabi)) = target {
        cmd.arg(format!("--target={triple}"))
            .arg("-nostdlib")
            .arg("-ffreestanding")
            .arg("-fno-pic")
            .arg("-fno-pie");
        if !march.is_empty() {
            cmd.arg(march).arg(mabi);
            if triple.starts_with("riscv") {
                cmd.arg("-mcmodel=medany");
            }
        }
        if triple.contains("x86_64") {
            cmd.arg("-mno-red-zone");
        }
    } else {
        cmd.arg("-ffunction-sections").arg("-fdata-sections");
    }

    let output = cmd.output().map_err(|e| format!("compile inline asm C ({cc}): {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "compile inline asm C failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    Ok(Some(out))
}

//! Raw `asm { }` block text contract for the LLVM path
//! (doc/05_design/os/hal/asm_embedded_hal_and_dual_run.md A.3 / A.4).
//!
//! A raw block is opaque assembler text: no operand substitution happens.
//! LLVM's inline-asm template engine, however, reads `$N` as an operand
//! reference and `${...}` as a modifier, so an AT&T immediate such as
//! `and $~0xF, %rsp` pasted verbatim aborts llc with
//! `Bad $ operand number in inline asm string`.  The escaping rule settled
//! by the design is: every `$` in a raw block becomes `$$` before the text
//! reaches LLVM.
//!
//! The escape itself lives in `crate::mir::asm_operands::escape_raw_asm_dollars`
//! and runs at MIR LOWERING, deliberately BEFORE `rewrite_asm_placeholders`
//! inserts the `$N` operand references — escaping afterwards would turn those
//! placeholders into literal `$$N` and unbind every operand.  By the time the
//! text reaches this module it is already escaped, so joining is all that is
//! left to do.
//!
//! Braces need no escaping in an LLVM IR inline-asm string (the `{ | }`
//! dialect-variant syntax only applies to GCC-style asm that clang has
//! already pre-escaped); the design's `{{`/`}}` rule is the Rust `asm!`
//! convention and is recorded as an erratum, not implemented.

/// Join already-escaped raw-block lines into one LLVM inline-asm template.
pub(crate) fn raw_asm_template(instructions: &[String]) -> String {
    instructions.join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lines_join_with_newlines_and_are_not_re_escaped() {
        // Input is post-escape text (see module docs): `$$` must survive as-is.
        let lines = vec!["and $$~0xF, %rsp".to_string(), "mov $$1, %eax".to_string()];
        assert_eq!(raw_asm_template(&lines), "and $$~0xF, %rsp\nmov $$1, %eax");
    }

    #[test]
    fn text_without_dollar_is_unchanged() {
        let lines = vec!["xor %rbp, %rbp".to_string(), "ud2".to_string()];
        assert_eq!(raw_asm_template(&lines), "xor %rbp, %rbp\nud2");
    }
}

# native (entry-closure): struct text fields misrender in string interpolation

- **Date:** 2026-07-23  **Status:** SOURCE FIXED; staged execution pending
- **Severity:** medium — no crash; wrong output when interpolating struct
  text fields. Comparisons/assignments appear functional.

## Repro (W83)
```
struct ReproOptions:
    log_mode: text
    quiet: bool
fn repro_defaults() -> ReproOptions: ReproOptions(log_mode: "human", quiet: false)
var opts = repro_defaults()
print "mode0={opts.log_mode}"      # prints mode0=2099601  (rodata POINTER as int)
opts.log_mode = "llm"
print "mode1={opts.log_mode} quiet={opts.quiet}"  # prints mode1=1 quiet=1
```
Expected `mode0=human mode1=llm quiet=true`.

## Analysis
Field read loses the text type: interpolation's coerce_concat_operand sees i64
and routes through rt_raw_i64_to_string, rendering the char* pointer value
(0x200A91-style) or a stale temp. Same family as the module-const typing fix
(Str consts needed Opaque("str") dest type) — struct field loads need their
declared field type threaded to the interpolation coercion.

## Impact scoping
simple_lsp_mcp uses struct text fields only in compares/assignments on the
startup path (post class→struct conversion), so the LSP server is expected
functional; fix before relying on interpolated struct text fields in natives.

## Resolution (2026-07-24)

Current MIR field projection recovers the owning struct's declared field
representation before `emit_get_field`, emits text fields as `Opaque("str")`,
and retains the declared HIR type on the projected local. This routes
interpolation through text conversion instead of rendering the pointer as an
integer.

The exact W83 before/after assignment oracle now lives in
`native_crossmodule_result_u8/main.spl`, which feeds hosted LLVM/Cranelift,
FreeBSD, AArch64/RISC-V64 execution, and ARM32/RV32/Windows-ARM64 object gates.
A focused source contract pins both type-propagation steps. Rebuilt execution
remains pending.

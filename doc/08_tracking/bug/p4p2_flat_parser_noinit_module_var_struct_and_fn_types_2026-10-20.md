# Self-hosted flat parser rejects initializer-less struct/fn-typed module vars (seed accepts)

- **Date:** 2026-10-20
- **Status:** open — tagged source workaround active; no root fix yet
- **Found by:** p4-phase2 lane (producer7 `87b9c74ff39`, source origin/release_phase3 `97aa8eb9e1f`)

## Failure

```
error: parse error in .../src/os/kernel/interrupts/idt.spl: 97:33:expected =, got Newline ''
```

The failing line is `var idt_entries: [IdtEntry; 256]`. The next lines would
fail the same way: `var idt_pointer: IdtPtr` and
`var handler_table: [fn(TaskContext); 256]`.

## Root cause

`parse_var_decl` (`src/compiler/10.frontend/core/parser_decls_use.spl:401`)
accepts `var g: [T; N]` with no initializer only when
`fixed_array_no_init_default_expr` can synthesize a zero default. It can do that
only for scalar element types. Every other type keeps the required `=`.

The Rust seed lowers any initializer-less `var name: [T; N]` to a zero-filled
global (`hir/lower/module_lowering/module_pass.rs`). Kernel code relies on that
zeroed-BSS meaning, so the self-hosted frontend cannot parse such files.

Census at `97aa8eb9e1f`: 121 initializer-less module vars in 12 `src/os` files,
plus 6 in `src/lib/nogc_async_mut_noalloc/baremetal`. Only `idt.spl` is in the
bootstrap_main closure.

## Workaround

Tagged `@workaround bug=p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20`
in `src/os/kernel/interrupts/idt.spl`, commit `8b7cfa3a43c`. The fix adds
explicit initializers with the same not-present entries and the same
`_default_handler` that `init_idt` writes before use, so the kernel sees the
same values. The original form is `97aa8eb9e1f:src/os/kernel/interrupts/idt.spl:97-102`.

## Root fix (owner decision needed)

Two options:

- Give struct and fn element types (and plain struct vars) a parser-synthesized
  zero value, matching the seed.
- Make initializers mandatory in the language and migrate the 127 sites.

Either one needs a producer rebuild.

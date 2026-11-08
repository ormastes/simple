# No-initializer module var of class/enum/imported/later-declared type still defaults to nil

- **Date:** 2026-11-09
- **Status:** open
- **Parent:** p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20 (PR #7871)

The flat parser zero-initializes `var g: S` and `[S; N]` only when `S` is a
struct declared EARLIER in the same module (it needs the field list). Class,
enum, imported, and later-declared types keep the nil-until-assignment fallback,
which conflicts with the owner decision (module var without initializer ->
zero/default; nil only in unsafe).

Fix needs type information, so it belongs in a HIR pass: after name resolution,
synthesize the zero value (recursive field zero, error naming the field when a
field has no safe zero) for any initializer-less module var, then drop the
parser nil fallback in `struct_zero_expr_v1` callers (parser_stmts.spl,
parser_decls_use.spl).

## 2026-11-09 kernel/noalloc gap (PR #7871 review)
Zero struct-literal init is disabled for sources whose path contains `/os/`, `noalloc` or `baremetal`
(driver `set_noinit_kernel_module_v1`): those modules keep the nil zero-BSS global, e.g.
`src/os/kernel/interrupts/gdt.spl` `var tss: TssEntry`. A struct literal there could need runtime
init/heap before the allocator exists, and no native objdump/boot gate could be run on this host to
show a static-zero landing. Open: prove static-zero emission (or an HIR zero pass) then lift the gate.

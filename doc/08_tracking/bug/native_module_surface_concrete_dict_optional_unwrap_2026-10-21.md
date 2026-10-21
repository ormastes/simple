# Concrete ParserModule dictionary values wrongly enter optional unwrapping

Date: 2026-10-21
Status: source repair authored; native verification pending.

## Observed failure

The v9 HIR ownership diagnostic built successfully, then received SIGSEGV in
`ModuleSurfaceBuilder.add_parsed_canonical`. The actual failing instruction at
binary-relative address `0x1bfc20` was `ldp q1, q0, [x8]`, the first record-copy
load from its concrete `ParserModule` argument. GDB recorded both `x1` and `x8`
as **0x1555555ee7c6**, outside the mapped heap. Other arguments, including the
builder, SourceFile and canonical path, remained ordinary heap addresses.

The caller was `module_surfaces_from_modules`, whose source dictionary is
`Dict<text, ParserModule>`. Its source loop already checks dictionary membership
and rejects nil entries. Nevertheless, it subsequently used
`if val present_module = module` on the concrete value. The alias loop used the
same optional-pattern transport.

## Native instruction evidence

The v9 caller performs:

- `0x1be2bc`: `rt_dict_get`, saving the returned record carrier.
- `0x1be2d0`: `rt_is_some` on that carrier.
- `0x1be2dc`: `rt_unwrap_or_self`; its returned value is discarded.
- `0x1be2e0`: reload the original carrier.
- `0x1be2e4`: `rt_value_as_int_wide`, then save that result as the concrete module.
- `0x1be1dc`: pass the resulting value to `add_parsed_canonical`.

The integer conversion shifts a tagged record carrier right by three, producing
the invalid pointer-shaped integer subsequently dereferenced by the concrete
record-copy prologue. This is a concrete/optional transport mismatch, not source
recursion. GDB's repeated caller-address backtrace frames alone do not establish
recursive execution; neither the source nor this call site calls itself.

## Source repair and limits

Keep the source-loop membership and nil checks, bind the dictionary lookup as
`ParserModule`, and pass that concrete value directly. Remove the optional
pattern around both source and alias loop bodies. Preserve all existing
canonical source, declaration-conflict, alias-ambiguity and missing-entry
diagnostics.

The existing native fixture exercises both physical-source registration and an
alias of the same provider. Its parser/lowering guards and diagnostic printing
remain intact. No build or acceptance test was run by the repair author. The v9
binary predates the repair and cannot qualify it. This focused repair does not
claim to fix the producer's general optional-pattern code generation.

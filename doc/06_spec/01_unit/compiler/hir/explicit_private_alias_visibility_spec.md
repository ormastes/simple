# Explicit private alias targets

Executable source: `test/01_unit/compiler/hir/explicit_private_alias_visibility_spec.spl`.

Status: nine frontend/HIR cases authored, **UNRUN**.

The cases reject private direct/nested targets, alias-owned defaults and bounds,
private intermediate aliases, and direct selective imports from another file.
They preserve caller-private generic arguments, neutral formal shadowing, and
public targets. Inputs use the actual frontend and HIR lowering owners.

Imported aliases sharing canonical target IDs still need selected-binding
authority. These negative checks do not establish positive module access or
complete namespace, glob, member, late-lookup, or exported-signature behavior.

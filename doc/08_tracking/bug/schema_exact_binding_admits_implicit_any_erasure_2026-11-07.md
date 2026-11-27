# Exact schema binding admitted implicit Any erasure

**Status:** verification pending; source repair and authored regressions.
**Source base:** `68a6f89671421a65a1b99faba1b76cba592850eb`.

The ordinary HIR type owner deliberately lowers an unresolved single uppercase
name such as Q to `HirTypeKind.Any` without an error. Its declaration lookup
precedes this fallback, so an actually declared nominal Q still binds normally.
Some argless container annotations also contain Any. The schema binder checked
only owner diagnostics before invoking a representational serializer that
correctly supports Any. As a result, a parsed schema field `value: Q`, including
`value: [Q]`, could acquire a valid structural identity despite missing concrete
type binding. A source consumer's ban on explicitly written Any did not cover
this implicit erasure.

The source path proves the defect: `hir_lowering/types.spl`'s
`lower_named_kind` takes its single-uppercase fallback after symbol lookup;
`data_bind_type_identity_v1` previously called `data_type_identity_v1`, whose
Any case emitted the `any` constructor. This is source evidence; no admitted
runtime reproduction was available.

Concrete managed schemas now explicitly deny Any at every semantic child after
canonical lowering. The admission policy is threaded through the existing
bounded projector, including aliases/defaults already expanded by their owner,
nominal arguments, containers, function parameters/results and Throws payloads.
There is no separate name resolver, descriptor-string filter or unbounded
preliminary traversal. The transport serializer and ordinary language Any
semantics are preserved. Explicit Any remains unsupported for this concrete
schema slice even where ordinary unsafe type-erasure policy permits it.

Five new authored scenarios cover actual parsed Q/nested Q and bare-container
erasure, explicit unsafe-permitted Any, parsed alias targets/defaults with
concrete overrides, declared nominal Q controls, and all accepted semantic
child families with function/effect controls. Source consumer integration adds
its own parsed source negatives in the independently owned W1b lane.

All new Simple tests, parser/HIR runtime execution, compiler/MCP smoke checks,
coverage and full W1 admission remain UNEXECUTED pending an exact admitted
producer. No Rust seed fallback, build, cache mutation or qualification PASS was
used for this repair.

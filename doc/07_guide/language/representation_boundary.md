# Representation boundary manifests

Source implementation candidate; executable qualification is **UNRUN**.

`@representation_boundary` records the exact declaration's reason, reviewers,
and audited capability upper bound. The attribute uses existing named literal
arguments and arrays:

```simple:skip
@representation_boundary(kind: "layout", reason: "Encode a device word", reviewers: ["layout-owner"], capabilities: [])
struct DeviceWord:
    bits: u32
```

Kinds are `ffi`, `layout`, `hardware`, and `intrinsics`. Reason and reviewer
entries must be nonempty. Capabilities use the existing `raw_ptr`, `ffi`,
`mmio`, `inline_asm`, and `type_erasure` vocabulary. Duplicate attributes,
keys, reviewer/capability entries, unknown fields, and malformed literal
shapes reject admission.

Supported owners are named functions, methods, extern functions, structs,
classes, and enums. An admitted callable exempts only its own internal
primitive bindings from MC011. A type covers its storage fields; its methods
and nested declarations have separate identities. Module/file wildcard scope
is rejected. Compatibility lint calls without an explicit project/source
context remain unexempt.
Named nested functions currently lower through the existing lambda-binding
route. They form exclusion barriers for the outer exemption; their own
annotation admission is unsupported until that route supplies exact callable
identity. A nested annotation therefore reports a diagnostic instead of
inheriting or manufacturing authority.
Methods declared under an `impl` reference without a lexical type owner also
remain unadmitted until that owner identity is resolved; no owner ID is guessed.

The live lint dispatcher binds the explicitly declared namespace from its
selected `simple.sdn` configuration. The explicit compiler API
`compile_file_with_representation_project_v1` supplies that selected project's
context for its exact input. Imported sources require their own resolved
owner; they do not inherit the root namespace. Missing/malformed authority
reports `E-MC-REP-002` when a declaration requests admission.
Normal CLI commands currently do not supply this selected-project compiler
context; their positive admission integration remains a follow-up. The live
lint dispatcher and explicit compiler API are the implemented entry surfaces.

Metadata diagnostics use baseline warning and critical denial. MC011 retains
its existing noncritical allow and critical warning policy. A manifest does
not grant unsafe capabilities. Each unsafe region still needs its explicit
caps, which must fit the owning manifest's audited upper bound. Raw extern
signatures keep MC001/public-type checking: reviewer text and an `ffi` kind
are not generated checked-wrapper evidence.

This candidate refuses flat-AST and HIR body cache/archive serialization for
modules with source-authored representation metadata. Ordinary unannotated
unsafe modules retain their existing body-cache eligibility. Missing reviewer
metadata is observed from actual unsafe HIR nodes on both cold and warm paths.
ABI signature projection remains available and conveys no exemption.
It rejects old codec versions instead of reusing dropped or stale authority.
The codec generator's opaque-carrier refusal is explicit; generator execution,
cache performance, compiler/MCP smoke, and runtime tests remain unqualified.
No automatic annotation insertion or invented reviewer/reason is provided.

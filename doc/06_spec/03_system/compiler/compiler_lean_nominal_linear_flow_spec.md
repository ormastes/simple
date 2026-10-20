# Exact nominal linear flow — compiler.backend.backend.lean_backend

Specification: `test/03_system/compiler/compiler_lean_nominal_linear_flow_spec.spl`. Requirement: C2 / REQ-MC-007 / NB-08. Status: 16 authored scenarios, all **UNRUN**; this is a manually maintained source manual, not SPipe-generated or runtime evidence.

The suite builds real typed `MirModule` inputs and exercises both full and regeneration APIs from `compiler.backend.backend.lean_backend`. Positive cases also compare the exact shared nominal-body result, including ordered lets and qualified declarations. Negative cases require `Err` from both module APIs; success causes failure. No Lean kernel or native compiler is invoked by authoring these files.

| Step | Actual assertion |
|---|---|
| Follow typed edges | Construct/project/return in the real path order |
| Preserve entry identity | Reordered storage with nonzero entry emits the exact same body |
| Traverse empty blocks | An empty intermediate Goto preserves the exact output |
| Carry enum payload | A predecessor struct becomes the successor enum payload |
| Preserve valid moves | Move to a fresh nominal local remains usable downstream |
| Keep zero-argument control | Nullary enum flow validates an empty parameter list |
| Keep scalar fallback | A scalar-only block still uses its original translator |
| Reject missing entry | Negative/missing selected IDs fail without output |
| Reject malformed IDs | Duplicate and negative block IDs fail |
| Reject missing target | Dangling successor returns a precise error |
| Reject cycles | Self and multi-block cycles fail before emission |
| Reject discarded blocks | A returning path cannot silently ignore disconnected code |
| Retain branch boundary | Merging If and Switch remain explicitly unsupported |
| Keep consumed state | Predecessor Move prevents successor reuse |
| Keep definitions | Cross-edge redefinition and early use fail |
| Keep exact types | Projection and final return retain signed MIR identity |

The setup reuses the actual MIR schemas and the existing backend factory. All checks use builtin SSpec assertions. Errors are checked for their precise cause, not merely absence of a rendered body. Byte/string rendering is observed at the production API; the helper does not implement translation. Existing proof-boundary comments and unavailable trust gates grant no proof authority.

Full recursive/union/general-branch/merge/loop/call/mutation semantics, production refinement, C1/C6/C7, generated-Lean execution and resource measurements remain open. Logical path storage is bounded by the actual input block array; no measured allocation or performance guarantee is inferred.

# C2 linear nominal flow: NB-08

This extends the selected generic formal plan's aggregate-flow requirement after PR #3974. It is an intermediate required subitem, not a substitute for full C2. The immutable source baseline is `af10a7acd2ffa5fe9e487cf3c5bd15fcc4aa5c2a`; the prior packet and source review remain unchanged.

## Source contract

The shared production API remains `translate_mir_nominal_body(MirFunction, LeanTypeContext) -> Result<text, CompileError>`. No new public interface or wire format is introduced. Internal `nominal_linear_block_order(MirBody, i64)` returns actual array indices only after validating the whole path.

1. Build one module-local-to-call map of block IDs to array indices, rejecting negative/duplicate IDs. Require the actual selected entry.
2. Walk only `Goto` edges, recording visited IDs and ordered indices. Every target must exist; revisiting an ID rejects a cycle. A `Ret` is accepted only when the ordered array's length equals the body's block count. Other terminators reject. No `Dict.len`, keys snapshot, graph recursion or branch enumeration is used.
3. Validate the existing exact signature/local environment, then emit each indexed block exactly once with the same `LeanNominalBodyEmitter`. The final `Ret` is checked against the retained return type. Definitions and move consumption are never reset at block boundaries.
4. Any failure returns `Err`; the public backend builder remains local and returns no partial generated source. Existing non-nominal dispatch remains unchanged.

The plan stores integer indices rather than copying MIR blocks or emitters. Additional logical memory is O(B) for the index, membership map and ordered array. Additional logical work is O(B) dictionary operations plus the existing O(I) emission pass. Dictionary hashing and language allocation/copy costs are not measured; no wall-time/RSS/performance PASS is claimed. The pre-existing instruction scan and declaration planning costs remain. There is no global state/cache or growing cross-request retention.

## Acceptance and actual test routes

Two SSpec owners independently import the plugin and compiler backend facades. Each of 16 scenarios invokes real full/generated `MirModule` export; successful scenarios also compare the exact shared body API output. Public inputs are real typed MIR definitions, signatures, blocks, instructions and operands. No stand-in renderer, helper that returns expected output, runner or toolchain is added.

Positive controls cover construction/projection/return, reordered storage with nonzero entry, empty intermediate block, enum payload, legal cross-edge Move, zero-argument nullary enum, and unchanged scalar-only fallback. Negative controls cover missing/negative entry, duplicate/negative IDs, missing successor, self/multi-block cycles, disconnected block, If/Switch, cross-edge consumed local, redefinition/early use and signedness mismatch on projection/return.

Tests were authored before production; expected baseline refusal is source-predicted RED only. All 32 new cases and all existing runtime, compiler, Lean, SPipe/manual-generation and core/MCP checks are UNRUN. Manually authored matching docs are not generated execution evidence. Independent review is required, with at most three correction cycles.

## Full selected scope remains open

| Requirement | Current boundary |
|---|---|
| C1 typed VIR/provenance | This packet adds no artifact authentication, source-to-VIR authority or refinement proof. Existing implemented owners and open qualification remain. |
| C2 declarations | PR3974 source covers acyclic structs/enums. Recursive/mutually recursive declarations and unions remain required and unsupported. |
| C2 body flow | This packet adds exact linear Goto paths only. Branches, merges/phi, enum elimination, loops, calls and mutation remain required work; refusal is not feature completion. |
| C3–C5 | Existing effects, state, proof/constraint implementations are unchanged; this packet makes no new acceptance claim. |
| C6 trust/replay | Authenticated exact resolvers, fresh independent kernel evidence and production replay admission remain open. No policy/signing/workflow change. |
| C7 translation/native | No compiler refinement/native ABI proof. Unicode-scalar semantic Char and pending physical ABI obligations remain separate. |

A disjoint next source lane can extend the declaration planner's recursive type semantics, but must settle Lean positivity/inhabitation, nominal identity, dependency ordering and retained source metadata without weakening cycle rejection first. Union export requires an actual retained active-member/representation contract; treating it as an ordinary tagged enum would invent semantics. General branches require explicit path-sensitive ownership and merge authority rather than duplicating this linear emitter. These remain on the full plan, not deleted exclusions.

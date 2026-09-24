# L7 three-payload formal verification — TLDR

This additive capsule defines nine Lean roots for broker bounds, RR replacement,
journal replay/conflict, pin protection, and source-binding freshness. It also
defines eleven bounded Simple replay cases that call current compiler/cache
owners.

Current status is **authored, not admitted**:

- The 2026-09-11 audit finds the global three-file/invalidation guarantee
  MISSING: ordinary loading still walks imports; only the eligible cold-two/
  warm-three broker is bounded. RR routing, semantic completeness and host
  publication remain closed.
- Seven proposed invariants add consumed-facet reuse, complete old/new
  membership, coherent publication/recovery and conservative refusal. V1 nil
  RR history and textual field-layout under-capture are concrete source gaps;
  these new obligations are OPEN/U, not additional proven roots.

- The current receipt is `NotChecked`; individual roots can reach at most
  `ModelProven`, and no `SourceRefined` promotion exists.
- Current receipt issuance is closed as `NotChecked`; caller DTOs cannot mint
  model evidence without owner-backed proof/replay/mutant receipts.
- The official Lean 4.30.0 AArch64 toolchain is identified, but the bounded
  three-cycle gate stopped at a parser error. The parser fix and Astra's
  subsequent `LawfulBEq` correction are not rerun, so no theorem or axiom audit
  is admitted yet.
- No admitted self-hosted full CLI exists, so the focused SSpec was not run.
- Semantic/compiler equivalence, failed-read instrumentation, live authority,
  crash durability, native output, performance, and RSS remain OPEN.
- A torn checksum-valid final record without `\n` is quarantined and may report
  `accepted_bytes > input length`; never assert the opposite unconditionally.
- `generation_manifest` remains unsupported by the action-root journal.

See [the full architecture](three_payload_compile_formal_verification.md) and
the [agent plan](../03_plan/agent_tasks/three_payload_compile_formal_verification.md).

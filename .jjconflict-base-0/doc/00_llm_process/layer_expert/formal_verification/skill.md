# Formal Verification Layer Expert

## Layer contract

This layer owns proof/evidence semantics across compiler boundaries. It does
not own product behavior and cannot promote a model result directly to an
artifact claim. Its public boundary is the versioned FV2 interface set in
`doc/03_plan/agent_tasks/simple_formal_verification_2_0.md`.

The refinement direction is:

```text
expanded/woven source -> typed VIR/MIR -> proof obligations
-> checked compiler certificates -> backend/product evidence
-> independent replay over shipped artifact
```

Each arrow either has checked evidence or blocks. Textual names, guessed types,
wildcard lowering, generated-only proof intent, and stale cache entries carry
no authority.

## Ownership boundaries

- MIR evidence identities/admission: `src/compiler/50.mir/`
- optimizer preservation: `src/compiler/60.mir_opt/`
- target consumers: `src/compiler/70.backend/` and `src/compiler/95.interp/`
- Lean/trust/replay tools: `src/compiler/90.tools/verify/`
- durable proofs: lane-specific manual files under `src/verification/`
- executable evidence: `test/`, mirrored by generated Markdown under
  `doc/06_spec/`

Do not place transient backend material in VIR/MIR evidence records. A backend
that cannot consume an admitted evidence opcode must reject before emitting a
successful artifact. When a lane crosses software and RTL, require both the
Lean/manual proof entry point and the RVFI/SymbiYosys evidence gate.

## Review checklist

1. Exact source, semantic, tool, compiler, proof, trust, and artifact identities
   are present and version-compatible.
2. Every reachable construct is exact, explicitly refined/contracted, or
   rejected; no implicit fallback exists.
3. Optimizers preserve evidence operands and transitive producers.
4. Regeneration preserves the manual proof contract and invalidates stale
   caches when exported identities change.
5. Missing tools, timeout, `unknown`, `sorry`, `admit`, undeclared trust, or
   replay mismatch blocks promotion.
6. System scenarios use the frozen FV2 steps/helpers and real assertions.
7. Current-main executed evidence, not abandoned history, determines status.

Coordinate target-local changes with the MIR-lowering, backend, compiler-driver,
bootstrap, or hardware-RTL layer expert as appropriate. The FV2 merge owner
resolves cross-layer interface changes; the independent final reviewer accepts
done marks.

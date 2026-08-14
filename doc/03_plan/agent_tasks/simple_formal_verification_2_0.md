# Simple Formal Verification 2.0 — Integration Plan

**Status:** Active replacement lane (2026-08-14)
**Merge owner:** This isolated detached worktree
**Final reviewer:** `$verify` production-readiness gate

## Current scope

Land the remaining fail-closed MIR evidence bridge without importing unrelated
work from the abandoned integration history. The bridge introduces explicit MIR
coverage-probe opcodes, preserves their operands and liveness through every
optimizer path, and lowers or interprets them explicitly. Unknown or malformed
evidence must reject; it must never disappear as dead metadata or silently
become a successful proof claim.

## Acceptance items

- [x] MIR declares the evidence probe opcodes and their operand contracts.
- [x] Admission rejects malformed shapes and valid-but-unlowered probe rows with
  distinct diagnostics.
- [x] MIR JSON retains the opcode and operands deterministically.
- [x] Optimization, inlining, visitor, SSA, and DCE paths preserve probe
  operands, including transitive and compatibility liveness.
- [x] Interpreter and LLVM-backed lowering handle each admitted probe explicitly.
- [x] Focused executable coverage covers serialization plus malformed,
  dropped-operand, transitive-liveness, and compatibility-liveness negatives.
- [x] The mirrored manual is current and contains no placeholder evidence.
- [ ] Compiler/core/MCP regression gates and formal proof gates pass once.
- [ ] Verification reports zero stubs, direct-runtime boundary violations, or
  numbered artifacts.
- [ ] Intentional changes are committed, rebased onto fetched `origin/main`,
  pushed as `HEAD:main` under `/tmp/simple-main-restart12-push.lock`, and proven
  reachable from the refetched remote tip.

## Current blockers and decisions

- The prior Formal Verification 2.0 history is not reachable from `origin/main`
  and contains broad unrelated work. Only the bounded MIR evidence commits are
  candidates for recovery; wholesale history import is prohibited.
- The self-hosted runtime is authoritative. Rust-seed success cannot substitute
  for a failed or unavailable pure-Simple check. Current blocker: the deployed
  `bin/release/simple` rejects its bounded ABI probe, so executable Simple gates
  cannot claim PASS in this worktree until deployment is repaired.
- Formal claims remain fail closed: this bridge transports evidence identity and
  liveness; it does not by itself promote model proofs to artifact verification.
- Verification is capped at three fix cycles, and each acceptance command runs
  at most once after it passes.

## Execution order

1. Recover and review the bounded MIR evidence changes against current main.
2. Resolve current-main API conflicts without weakening opcode or liveness rules.
3. Run the focused spec and generate/review its mirrored manual.
4. Run the required compiler/core/MCP, formal, audit, stub, and layout gates.
5. Commit, serialize fetch/rebase/push, refetch, prove reachability, clean the
   worktree, then write `/tmp/restart12-formal.done`.

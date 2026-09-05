# Feature: mac-metal-bootstrap-mcp

## Raw Request
$sp_dev sync gh. check todo and plan only can do in metal. imple them all; fix MCP handshaking failure.

## Task Type
todo

## Refined Goal
Close TODO 119 on macOS with a deployable pure-Simple CLI, verified Metal queue evidence, and a correlated MCP stdio handshake.

## Acceptance Criteria
- AC-1: A fresh full bootstrap deploys `bin/simple`, and the normal symlink path passes `-c 'print(1+1)'` plus every executable redeploy-gate check.
- AC-2: The deployed binary provenance records path, timestamp, SHA-256, architecture, and the exact bootstrap command.
- AC-3: The host GPU queue roundtrip and production GUI/web host-GPU queue wrapper pass with native Metal readback.
- AC-4: The generated MCP wrapper preserves numeric and string JSON-RPC request IDs, and the full MCP stdio integration test passes.
- AC-5: The plan, guide, report, TODO row, and normal-model review record the final evidence before TODO 119 closes.

## Scope Exclusions
Non-Metal GPU backends and unrelated fullscreen/browser worktree changes.

## Cooperative Review
Merge owner: Codex main workspace owner. Final reviewer: normal/highest-capability model. Sidecars are N/A because the remaining failures share one bootstrap/deploy boundary and require serial binary evidence.

## Runtime Boundary Decision
- runtime_need: None; the deployed CLI already supports a sibling seed delegate.
- facade_checked: `scripts/setup/setup.shs` owns the `bin/simple` release symlink layout.
- chosen_path: reuse-facade by creating the matching `bin/simple_seed` release symlink.
- rejected_shortcuts: no new `rt_*`, no shell `readlink`, no fixture-only bypass, no copied seed at `bin/simple`, and no deploy-gate relaxation.

## Phase
verifying

## Log
- dev: Refined the Metal/bootstrap/MCP closure lane into five acceptance criteria.
- implement: Reproduced deploy false-positive caused by setup omitting the sibling seed symlink; added post-setup smoke with rollback.
- implement: Added relative argv0 normalization, semicolon statement separation, value-type parameter copying, indexed-object field assignment, and host-aware cfg dispatch checks.
- implement: Fixed bootstrap MIR parameter fallback IDs after preserved LLVM IR proved `%l1` was undefined for signature argument `%l0`.
- implement: Replaced the unavailable bootstrap-env discriminator with the builder-derived return-local offset after cycle 2 reproduced the same `%l1` IR.
- verify-cycle-1: Stage 2 failed because `/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T/simple_llvm_89283.ll` referenced undefined `%l1` while the function signature defined `%l0`; Stage 4 fallback was terminated after preserving cache and IR.
- verify-cycle-2: After the bootstrap-env fallback fix, `/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T/simple_llvm_79731.ll` reproduced the identical `%l1` defect.
- verify-cycle-3: After deriving the offset structurally, `/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T/simple_llvm_18905.ll` still reproduced the undefined `%l1` IR. The preserved files differ in ordering/hash, so they prove the parameter-mapping defect but do not by themselves prove cache staleness.
- verify-fresh-cache: A single `--fresh-cache` run still failed Stage 2 and Stage 3. The fallback Stage 4 build was stopped on request; no candidate was deployed and AC-1/AC-2 remain open.
- verify-mcp: The tracked setup source and generated default wrapper passed numeric/string request-ID correlation; the separate full-server integration also passed (`3 examples, 0 failures`). The source contract rejects nested `params.id`, and the native smoke gates the default wrapper separately so `SIMPLE_MCP_FULL=1` cannot bypass this regression.

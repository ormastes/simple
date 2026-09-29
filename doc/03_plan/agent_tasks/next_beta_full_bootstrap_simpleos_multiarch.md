<!-- codex-design -->
# Agent Tasks — Next Beta Full Bootstrap and SimpleOS Multiarch

## Shared contract frozen by merge owner

Job IDs, architecture IDs, receipt prefix, manual step text, and test helper
names are defined in
`doc/05_design/next_beta_full_bootstrap_simpleos_multiarch.md`. Any placeholder
must use `fail(...)` or `assert(false)` until implemented.

## Lanes

| Lane | Scope | Sidecar | Owner/output |
|---|---|---|---|
| A | Version/tag/prerelease and exact asset preflight | N/A; narrow workflow lane | primary Codex |
| B | Strict host full-bootstrap matrix and memory receipts | prior read-only bootstrap research merged | primary Codex |
| C | SimpleOS x86_64/AArch64/RISC-V64 matrix and packages | prior read-only target/CI research merged | primary Codex |
| D | SPipe source contract and generated manual | N/A; one spec | primary Codex |
| E | Local bootstrap, QEMU, memory, whole-test verification | N/A; authoritative execution | primary Codex |
| F | GitHub Actions and published-release verification | N/A; remote authoritative execution | primary Codex |

No lower-model implementation sidecar is planned because the shared worktree
has concurrent compiler/memory/rendering edits and workflow ownership must stay
singular. Earlier research sidecars were read-only and reviewed by the primary
model.

Merge owner: primary Codex (`/root`).

Final reviewer: best available normal/highest-capability Codex after all lanes
merge; it owns generated-manual quality, exclusions, coverage, and done marks.

## Task order

1. Add failing source-contract SPipe for REQ-001..REQ-005.
2. Harden version/tag/prerelease checks.
3. Make host bootstrap matrix fail closed.
4. Wire stage-4 resource gates and receipts.
5. Convert SimpleOS release to the required three-architecture matrix.
6. Add exact preflight and post-publication verification.
7. Update process/guide docs.
8. Run focused checks, then one full bounded verification pass.
9. Perform local release preparation and request push approval.
10. Push, observe, and repair GitHub failures within three cycles.

## Worktree rule

Before every edit/commit, inspect ownership. Do not absorb unrelated dirty
compiler, memory, rendering, tooling, or evidence files. If required bootstrap
fixes overlap an active lane, coordinate ownership or wait for that lane's
reviewed result.

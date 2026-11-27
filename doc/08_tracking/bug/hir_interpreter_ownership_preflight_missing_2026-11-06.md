# HIR interpreter ownership preflight missing

Status: open; owner Codex memory lane. Base77b05b3. Source-confirmed at
`src/compiler/70.backend/backend/interpreter.spl:128`: process_module creates an
Environment without running CFG ownership validation; driver.spl executes modules
sequentially. Strict parameter-effect admission is not local move validation.
Existing MIR OwnershipFlow is the reusable pure-Simple owner; no runtime fix or
Rust seed fallback is justified. Executable reproduction awaits an admitted tool.

Repair: typed HIR adapter builds Read/Move/Revive/Write facts and CFG edges for existing
OwnershipFlow; driver checks the entire retained closure before any execution and
the backend checks direct calls. Unsupported ownership forms and budget exhaustion
reject strict modules explicitly. Legacy modules retain their old behavior.
No target MIR is built and no source spelling is used as ownership authority.

Rooted ownership, full loans/drop elaboration, core-interpreter routing and SMF
artifact admission remain separate open requirements. Tokens/provider telemetry
unavailable; no ratio inferred. Do not close without real positive/negative
source-to-entry execution plus current-producer receipts.

Imported short contracts now use compact physical source/body/effect admission receipts and one live provider verification index. Bounds exhaustion and changed receipts reject. The cycle2 findings and cycle4 ordering repair are source-reviewed; runtime regressions remain NOT_RUN.

Cycle4 is a targeted repair of review3's classifier-before-bounds finding. The
user AGENTS.md permits at most6 verify/fix cycles and takes precedence over the
earlier stricter3-cycle lane guidance; count3 is retained, not reset. Every strict
module ingress now encodes the complete typed HIR under the canonical guarded
work/depth quota before CFG capture or recursive classifiers, and charges that
work against the module budget. Projected expression type classification also
requires bounded type identity first. Deep Optional/Result/Tuple parameter and
projection rejection specs are authored, NOT_RUN. Targeted review4 closed the
ordering finding statically; the four prior cycles remain counted and at most
two further cycles remain under the user cap.

2026-11-07 reconciliation: the saved source repair at dd3444e346d4 is being
reconciled onto release b065ff00f44e in an isolated memory-HIR lane. Review4
previously closed the classifier ordering finding by source inspection only;
the reconciliation source review is clean, conditional on current codec integration. The four
prior repair cycles remain counted, leaving at most two additional cycles.
Current release edits are preserved through three-way reconciliation. Only the
ownership context fields are imported into CompileContext; unrelated source
analysis and diagnostic collection work from the saved draft is excluded.
The codec owner separately reconciles bounded traversal onto all current codec
declarations. This lane cannot be runtime-admitted without that dependency.
Unit, actual CLI integration, and required core checks remain NOT_RUN pending
root admission of an exact current producer. No release qualification is claimed.

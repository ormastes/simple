# Item 5 development evidence ledger

Status: BLOCKED / TEST_BLOCKED. No item completion, production PASS,
verified RED/GREEN, implementation PR/merge, release admission or publication
is claimed. Documentation is separately reviewed for landing.

Research: additive local/domain item5_provider_size_2026-10-02 documents.
Architecture: compiler/perf/item5_provider_activation_and_closure_2026-10-02.
Design: compiler/perf/item5_provider_size_research_design_2026-10-02.
Acceptance: sys_test/item5_provider_size_acceptance_2026-10-02 (I5-01..14).
Ownership: agent_tasks/item5_provider_size_tdd_2026-10-02.
Release comparison: compiler/perf/item5_release_review_2026-10-02.

## Authored behavioral lane

Worktree C:/dev/simple-item5-admission-20261002 owns I5-04 source/tests and
its bug evidence note. Parent inspected the exact diff: admission binds every
pinned member's name/offset/extent/payload digest and rejects out-of-bounds
geometry before receipt publication. Tests first authored a valid canonical
ten-section image/receipt fixture and identity mutations, then the minimal
validation was added. Positive admission/reuse and typed failure/cache checks
exercise production calls. This is authoring order, not executed TDD evidence.

git diff --check passed in that lane (formatting only). Tests/checks/lint,
manual generation, core/MCP/LSP runtime checks and release cohorts are NOT RUN.
The reviewed diff remains uncommitted and is not admitted for landing. Parent
review also checked a zero-sized archive with a nonzero first section offset,
covering the offset guard independently of extent overflow. Main-based session
git diff --check passed once before final annotation cleanup; no runtime result
is inferred from formatting. Generated manuals must be refreshed by the admitted
runner after execution, before verification can pass.

## Execution facts and remaining work

bin/simple.exe --version on the main checkout reports a Rust-built bootstrap
seed. bin/release is absent. Bounded WSL discovery did not establish an admitted
runtime. An admitted self-hosted runtime identity and receipts are required
before observing behavioral RED/GREEN. Do not silently execute seed tests.

Additional live executable provenance was inspected read-only. The Cranelift
stage2-runtime-authority binary has SHA-256
f177b0bad1e65358ad5aa6f9e0548a871af1dd79d9aa2a036668bb75f3a43cf1;
its adjacent inputs stamp identifies it as a Rust/Cargo bootstrap seed.
The LLVM Stage2 candidate has SHA-256
b54b12f3b504e062f65482da58a488f94dad337a8e53aeec596731bab16ecd98;
native_probe/llvm80-phase2-canonical-sanity/launch.env explicitly records
admission=UNADMITTED and source_head=c9fb6afdd4f11febdd78a7398df3543324cd5300.
Neither is an admitted test runtime. Their live work was not invoked, modified
or restarted by this session.

Third consecutive goal-turn audit: bin/release remains absent. The LLVM sanity
process and supervisor are no longer live. sanity.receipt.env is terminal with
status=complete, reason=child-exit, raw_status=1 and native_exit_status=1;
stage2-sanity.env records status=fail and frontend_smoke_status=126. Its
candidate identity remains unchanged. The remaining live Cranelift authority
is the previously identified seed. No inspected state proves an admitted test
runtime. The goal is blocked pending an admitted runtime and its provenance,
or an explicit user-directed change to the execution constraint. Preserve all
authored work; do not restart another session's failed or live bootstrap.

Main isolated checkout session 58539 completed with exit 0. Reviewed member
authority source/tests and the bug note were copied from the separately owned
admission lane into the clean corresponding paths in the main-based session.
Additive research/design/plan documents were integrated; canonical plan,
architecture, detail design and seven-item umbrella link these updates.
Other-agent dirty main command files were left untouched.

Full remaining scope includes real activation, target/architecture/policy
binding, concurrent first demand, pure/foreign parity and rollback, exact NoGC
closure, release-small proof, compiled CLI provider cutover, packaging/lifetime,
all supported host/target evidence and matched size/startup/RSS cohorts.
The authored I5-04 fix does not waive any case. Resolve release destination,
preserve its repeated-error contract, renew evidence, review and integrate
through protected PR authority only after all applicable gates pass.

## 2026-10-03 resumed runtime audit and documentation landing lane

User requested resumption and self-landing of PRs. Documentation-only session:
owner Codex root, session item5-docs-20261003, worktree
C:/dev/simple-item5-docs-20261003, branch work/item5-docs-20261003, target main,
base/expected target e10963a3b065dde1643c777512c3988526973957. Its owned scope
is twelve Markdown files only. Source and executable tests remain outside
this documentation change. Their verification gate and the full goal remain
unresolved; merging documentation cannot certify implementation completion.

The fetched release/1.0 head is now
4c8a20414ca8b0c3b2a105727dbd065825897f2d. The authored release lane still binds
its original acaaef9906ecd16b25ec5d9c2a0b6eff5be1b92d base and must renew
target evidence before integration. Its provider-admission source is unchanged
between those release snapshots.

New read-only qualification evidence: LLVM candidate
32867ba1f9120406373cee55eb243e420e21740576d39c30a0b062a611932e8c
is UNPROVEN and fails its bounded p2_add parsing smoke (status 124).
Cranelift candidate
3dcbd17c0621939f62a6b94aae5ac58cd29672b278b3e027924aa4a8502b98fd
has failing qualification with workaround refresh reporting workaround Git
failed (-1); dependent smokes did not run. The production CLI logs that refresh
failure and continues, so this diagnostic alone does not establish the terminal
compiler failure's cause. Inspect the exact frozen source/producer and terminal
receipt before proposing a process-boundary repair. Neither candidate is an
admitted normal test runtime. Do not replace these failures with synthetic
evidence or broad rebuilds.

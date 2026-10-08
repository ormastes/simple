# Incremental build metadata requirements

<!-- codex-design -->

Status: design requirements derived from the user's supplied research and explicit instruction to prioritize it. Not an implementation or qualification claim. The original Windows RC1 bootstrap goal remains active in parallel.

Source: [supplied research](../../01_research/local/simple_compiler_incremental_build_tldr_scv_metadata_design_2026-10-08.md), SHA256 `128a5f947662e9d10bc8267aa57bac455a243251af29df4187df4f6be47b2b3a`. Preserve the Downloads original. These requirements adopt its stated scope; optional remote publication and automatic source commits remain disabled, not implicitly authorized by this design.

| ID | Required behavior |
| --- | --- |
| REQ-IM-001 | Standalone pure-Simple compilation remains correct without Git, SCV, IDE, Spipe, BuildRunner, TestRunner or a daemon. |
| REQ-IM-002 | One canonical edit-validation contract serves IDE, Spipe, SCV and filesystem reconciliation; SCV owns durable repository history when enabled. |
| REQ-IM-003 | Buffer, index, worktree and committed snapshots have distinct immutable identities. Event hints, timestamps and file existence never authorize reuse. |
| REQ-IM-004 | Reuse existing compiler snapshot, semantic cache, package TLDR and action-journal contracts; do not introduce competing authorities. |
| REQ-IM-005 | An unchanged imported module is consumed through its verified public summary; generic/inline/CTFE/macro/aspect body requirements are explicit digest-bound dependencies. |
| REQ-IM-006 | Parse changed source once per action generation, share the immutable AST/summary, and publish header readiness separately from object readiness. |
| REQ-IM-007 | Shared work has one publisher per full action identity, bounded waiters, fencing tokens and crash recovery. Ordinary failure and process crash remain distinct. |
| REQ-IM-008 | Invalidation covers content, public facets, initializer/effects, negative resolution queries, directory membership, static guards, producer/schema and relevant target/provider configuration. |
| REQ-IM-009 | AST sharing across hosts requires a portable schema and complete semantic input identity; MIR/object/runtime/link reuse remains phase-specific. |
| REQ-IM-010 | Required source, summary, object and link validation precedes atomic binary publication. Residual scoped freshness and tests may run afterward. |
| REQ-IM-011 | Binary readiness, TLDR verification, tests, SCM attachment and remote publication are independent states; mandatory gates require matching terminal evidence. |
| REQ-IM-012 | Metadata uses canonical SDN and bounded binary events, one WAL/lease owner, recoverable committed prefixes and additive migration. |
| REQ-IM-013 | Git notes/SCV receipts bind exact immutable revisions and coverage. Notes do not alter source identity; no automatic amend, tag-per-build, commit or remote push. |
| REQ-IM-014 | Hybrid SMF/CAS development storage preserves packed SMF compatibility and does not duplicate object payloads. Storage redesign follows correctness and hot-path work. |
| REQ-IM-015 | Bootstrap and tests continue independent work after failures, preserve valid successes, and retry only changed failed inputs with bounded attempts. |
| REQ-IM-016 | Measure pure-Simple standalone and managed builds separately; optimization must preserve output semantics, memory safety, bounded retention and diagnostics within the explicitly requested observer policy. Interface-only mode cannot claim full body-diagnostic coverage; full-diagnostics mode requires matching complete receipts or body validation. |

No user-interface redesign is requested. Proposed CLI names and optional receipt displays remain design surfaces until implementation and compatibility review.

See [architecture](../../04_architecture/incremental_build_metadata_20261008.md), [detail design](../../05_design/incremental_build_metadata_20261008.md), and [acceptance plan](../../03_plan/sys_test/incremental_build_metadata_20261008.md).

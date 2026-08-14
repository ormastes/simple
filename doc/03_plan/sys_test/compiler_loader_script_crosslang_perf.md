# Compiler loader, script, and packed-byte performance plan

## Plan status

Plan complete; feature verification blocked. This document is the canonical
handoff for `compiler_loader_script_crosslang_perf`. It records what is already
implemented, what current evidence proves, and the exact remaining gates. A
checked planning item means the handoff is specified, not that the underlying
feature gate passed.

## Goal

Prove that compiler loading retains negative resolutions without changing
resolution semantics, that interpreter `[u8]` values remain packed across
byte-preserving operations and safely widen at generic boundaries, and that
cross-language timing/RSS rows are admitted only from an exact self-hosted
compiler with semantic parity and no fallback.

## Scope and exclusions

In scope: resolver cache semantics and invalidation, failed file-existence
probe accounting, packed-byte interpreter behavior and foreign-call lifetime,
cross-language provenance/checksum/timing/RSS contracts, focused compiler and
MCP/LSP regression gates, documentation, and serialized integration.

Out of scope: substituting the Rust seed for Stage 4 evidence, claiming
filesystem syscall counts from facade counters, disabled-path assembly/cycle
claims, changing public byte-array semantics, rebuilding Stage 4 in this plan
lane, or absorbing unrelated GUI/web/2D files.

## Authoritative artifacts

| Artifact | Path | Current disposition |
|---|---|---|
| SPipe state | `.spipe/compiler_loader_script_crosslang_perf/state.md` | Current planning acceptance and review contract |
| Executable SSpec | `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl` | Present; declares REQ-001..008 and NFR-001..006 |
| Scenario manual | `doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md` | Present summary with operator flow; generated scenario sections/hash/docgen provenance remain blocked |
| Detail design | `doc/05_design/compiler_loader_script_crosslang_perf.md` | Partial: resolver/probe/RSS design present; packed storage/write-back/foreign capability design missing |
| Compiler performance guide | `doc/07_guide/compiler/check_perf.md` | Must identify this plan and its blocked self-hosted lane |
| Feature expert | `doc/00_llm_process/feature_expert/compiler_loader_script_crosslang_perf/skill.md` | Required knowledge handoff |
| Compiler layer expert | `doc/00_llm_process/layer_expert/compiler_driver/skill.md` | Must link this lane |
| Loader blocker | `doc/08_tracking/bug/module_loader_negative_cache_stat_storm_2026-08-11.md` | Open verification condition retained |
| Packed-byte history | `doc/08_tracking/bug/interpreter_byte_array_len_widening_spin_2026-08-13.md` | Fixed historical boundary/performance defect |
| Packed-byte evidence gaps | `doc/08_tracking/bug/compiler_loader_packed_byte_evidence_gaps_2026-08-14.md` | Open PBL-01/02/03 test names, anchors, and unblock commands |
| Retained harness | `scripts/check/check-cross-language-perf.shs` | Present |
| C facade selfcheck | `scripts/check/check-file-exists-probe-c.shs` | Present |

Artifact gaps are explicit: local research, domain research, selected feature
requirements, selected NFR requirements, and architecture are **MISSING**;
packed-byte detail design is **PARTIAL**. Their absence blocks feature/verify
completion and prevents the `@req` identifiers from being treated as fully
traced. This planning lane does not invent or auto-select requirements; a
future `$research` selection turn owns requirement choice and `$design` owns
architecture/detail-design completion.

## Acceptance matrix

| ID | Requirement coverage | Acceptance condition | Authoritative evidence | Current state |
|---|---|---|---|---|
| PBL-01 | REQ-008, NFR-003 | Index, slice, iteration, concat, clone, equality, freeze, and byte-valued mutation preserve packed storage; non-byte insertion widens once | `packed_byte_interpreter_semantics` plus focused driver mutator tests | BLOCKED — existing tests cover index/slice/iteration/mutators/widening/freeze; concat/clone/equality tests are missing and the prior session exhausted its three-cycle cap |
| PBL-02 | REQ-008, NFR-003 | Identifier and projected-place mutators write back, preserve COW aliases, return removed elements, reject immutable/frozen receivers | `src/compiler_rust/driver/tests/interpreter_extern.rs` focused tests | BLOCKED — identifier/COW/removed/frozen tests exist; projected-place evidence is missing and the focused lane is capped |
| PBL-03 | REQ-008, NFR-003/006 | Foreign packed-byte pointers are input-only, descriptor-bounded, nested adapters are scoped, and capabilities cannot escape a call | Focused `simple-compiler` unit tests at the byte-boundary/SFFI owner | MISSING: current tree has byte adapter tests but no complete capability lifetime/escape evidence set |
| LDR-01 | REQ-004/005/006/007, NFR-002 | Exact repeated miss caches once; adjacent callers remain distinct; reset invalidates; resolution result is unchanged | Focused SSpec and resolver unit coverage | BLOCKED — implementation is present; fresh admitted self-hosted execution is unavailable |
| LDR-02 | REQ-004/005, NFR-001/002/006 | 100 reset-per-request resolutions versus 1000 retained requests produce identical results, uncached counts 100/1, positive failed-probe baseline, and cached probes at most 10% | SSpec plus C facade selfcheck | BLOCKED — contracts are present; fresh admitted self-hosted measurement is unavailable |
| PRV-01 | REQ-001/003, NFR-005 | Exact executable path/hash and actual mode are admitted; seed, stale hash, requested/actual mismatch, and fallback are rejected before timing | SSpec and retained harness contract tests | CONTRADICTED — the deployed candidate exists but exit 139 on its test/help ABI path disproves admission |
| BYT-01 | REQ-001/002/008, NFR-003/004 | Native byte fixture validates 1/4/32 MiB length, boundaries, checksum, fixture timing, and RSS at no more than four times payload before admitting a row | SSpec, retained byte contract, and cross-language harness | BLOCKED — contract exists; live retained row requires an admitted candidate |
| XLG-01 | REQ-001/002, NFR-004 | C/Rust/Go/Python/Bun/Simple workloads have equivalent checksums, including `fib(35)=9227465`; unavailable peers remain unavailable | Retained schema/provenance/byte contract scripts | BLOCKED — contracts exist; fresh report requires an admitted candidate |
| CMP-01 | REQ-007, NFR-001/005/006 | Self-hosted compiler checks for `src/compiler`, `src/lib`, MCP, LSP, and MCP stdio smoke pass without seed fallback | Commands below | BLOCKED — deployed candidate exists but is not admitted |
| DOC-01 | all | Plan-facing summary, guide, feature/layer expert knowledge, blockers, and cooperative review are current; generated manual and traceability gaps stay explicit | Document review and layout guard | BLOCKED — plan-facing disposition and review are complete; generated manual, research, selected requirements, architecture, and live evidence remain outstanding |
| VCS-01 | all | Only intentional files are committed; integration uses `/tmp/simple-main-restart12-push.lock`; refreshed `origin/main` contains HEAD; tree is clean except separately owned concurrent files | Git receipts | BLOCKED — plan commit and serialized integration remain pending |

## Manual-facing flow

The executable spec owns these phrases. The mirrored manual must preserve this
order and be understandable without opening the `.spl` source:

1. `Check two deterministic missing facade calls`
2. `Prepare equivalent performance fixtures`
3. `Verify optimized paths preserve behavior and budgets`
4. `Measure failed existence probes at the file-exists facade`
5. `Audit C, Rust, and interpreter-provider probe contracts`
6. `Reject a preexisting fixture without deleting any path`
7. `Admit executable identity and execution modes`
8. `Compare cross-language semantic parity`
9. `Measure compiler loader and script rows`

Canonical existing checker helpers are
`scripts/check/check-file-exists-probe-c.shs` and
`scripts/check/check-cross-language-perf.shs`. Historical detached work named
`check-compiler-loader-perf.shs` and
`check-interpreter-packed-byte-rss.shs`, but those files are absent on current
`main`; the plan must not instruct operators to run them. Any replacement helper
must first land fail-closed with `assert(false)` or `fail(...)` placeholders,
then gain real oracles and its own deliberate-red contract.

## One-pass verification order

Run each unchanged green command once. A failing acceptance lane may receive at
most three distinct fix/verify cycles; never repeat an identical failed command.

1. Establish admitted tooling identity and retain its receipts:
   `mkdir -p build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf`;
   `test -x release/x86_64-unknown-linux-gnu/simple`;
   `sha256sum release/x86_64-unknown-linux-gnu/simple > build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf/stage4.sha256`;
   `release/x86_64-unknown-linux-gnu/simple --version > build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf/stage4-version.log 2>&1`;
   `release/x86_64-unknown-linux-gnu/simple test --help > build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf/stage4-test-help.log 2>&1`.
   Any nonzero exit, seed identity, missing target, or crash rejects admission.
   Repair/redeploy is owned by
   `doc/03_plan/compiler/bootstrap/redeploy_stage4_plan_2026-07-09.md` and
   `doc/08_tracking/bug/no_self_hosted_binary_deployed_blocks_bootstrap_gate_2026-08-09.md`.
2. Packed semantics:
   `cargo test -p simple-compiler --test packed_byte_interpreter_semantics`
   and `cargo test -p simple-driver --test interpreter_extern
   interpreter_byte_array_identifier_mutators -- --test-threads=1` from
   `src/compiler_rust`.
3. Foreign boundary unit evidence:
   from `src/compiler_rust`, run
   `cargo test -p simple-compiler interpreter_extern::sffi_array` and
   `cargo test -p simple-compiler --test packed_byte_foreign_capability_lifetime`.
   The latter fixed file and test names are specified in the tracking record.
4. Resolver/facade evidence:
   `sh scripts/check/check-file-exists-probe-c.shs`, then
   `release/x86_64-unknown-linux-gnu/simple test test/05_perf/compiler_loader_script_crosslang_perf_spec.spl
   --mode=interpreter --no-session-daemon` and require the authoritative file
   verdict with no dropped examples.
5. Retained harness contracts:
   `sh test/05_perf/profile_scripts/cross_language_compile_failure_contract_test.shs`;
   `sh test/05_perf/profile_scripts/cross_language_compiler_provenance_contract_test.shs`;
   `sh test/05_perf/profile_scripts/cross_language_byte_retained_contract_test.shs`;
   `sh test/05_perf/profile_scripts/cross_language_retained_schema_contract_test.shs`;
   then `RUN_TIMEOUT=30 SIMPLE_BINARY="$PWD/release/x86_64-unknown-linux-gnu/simple" REPORT_PATH="$PWD/build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf/cross_language_perf.md" sh scripts/check/check-cross-language-perf.shs`.
6. Compiler/tool-server surface:
   `release/x86_64-unknown-linux-gnu/simple check src/compiler`;
   `release/x86_64-unknown-linux-gnu/simple check src/lib`;
   `release/x86_64-unknown-linux-gnu/simple check src/app/mcp`;
   `release/x86_64-unknown-linux-gnu/simple check src/app/simple_lsp_mcp`; and
   `SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test
   test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter`.
7. Planning/document gates:
   `sh scripts/setup/install-spipe-dev-command.shs --check`,
   `find doc/06_spec -name '*_spec.spl' | wc -l` (must be `0`), and
   `sh scripts/audit/direct-env-runtime-guard.shs --working` plus `--staged`.

No optimizer command is required for this documentation-only plan completion;
future `.spl` implementation changes must run
`bin/simple run src/app/optimize/main.spl <file> --full --level=O3` and compare
the same correctness/performance baseline before and after.

## Blocker and resume ledger

| Blocked IDs | Missing prerequisite | Exact resume command | Retained artifacts | Owner | Final reviewer |
|---|---|---|---|---|---|
| PBL-01/02 | Fresh session after the previous three-cycle cap; tests named in `doc/08_tracking/bug/compiler_loader_packed_byte_evidence_gaps_2026-08-14.md` landed | `cd src/compiler_rust && cargo test -p simple-compiler --test packed_byte_interpreter_semantics && cargo test -p simple-driver --test interpreter_extern interpreter_byte_array_identifier_mutators -- --test-threads=1` | Full test logs and commit SHA | compiler-interpreter owner | highest-capability reviewer |
| PBL-03 | `src/compiler_rust/compiler/tests/packed_byte_foreign_capability_lifetime.rs` exists with the three named tests in the tracking record | `cd src/compiler_rust && cargo test -p simple-compiler --test packed_byte_foreign_capability_lifetime` | Test source, verdict, deliberate-red receipt | interpreter SFFI owner | highest-capability reviewer |
| LDR-01/02, PRV-01, BYT-01, XLG-01, CMP-01 | Repair/redeploy an admitted self-hosted Stage 4 CLI per the linked repair plan/TODO | `test -x release/x86_64-unknown-linux-gnu/simple && release/x86_64-unknown-linux-gnu/simple --version && release/x86_64-unknown-linux-gnu/simple test --help && sh scripts/check/check-file-exists-probe-c.shs && release/x86_64-unknown-linux-gnu/simple test test/05_perf/compiler_loader_script_crosslang_perf_spec.spl --mode=interpreter --no-session-daemon && RUN_TIMEOUT=30 SIMPLE_BINARY="$PWD/release/x86_64-unknown-linux-gnu/simple" REPORT_PATH="$PWD/build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf/cross_language_perf.md" sh scripts/check/check-cross-language-perf.shs && release/x86_64-unknown-linux-gnu/simple check src/compiler && release/x86_64-unknown-linux-gnu/simple check src/lib && release/x86_64-unknown-linux-gnu/simple check src/app/mcp && release/x86_64-unknown-linux-gnu/simple check src/app/simple_lsp_mcp && SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter` | Binary path/hash, version/help logs, checker/spec logs, retained profile report, RSS receipts | compiler-loader performance owner | highest-capability reviewer |
| DOC-01 traceability | User-selected feature/NFR requirements plus missing research and architecture artifacts | Invoke `$research compiler_loader_script_crosslang_perf`; stop for mandatory explicit user selection; delete unchosen options; then invoke `$design compiler_loader_script_crosslang_perf`. Required outputs are `doc/01_research/local/compiler_loader_script_crosslang_perf.md`, `doc/01_research/domain/compiler_loader_script_crosslang_perf.md`, `doc/02_requirements/feature/compiler_loader_script_crosslang_perf.md`, `doc/02_requirements/nfr/compiler_loader_script_crosslang_perf.md`, `doc/04_architecture/compiler_loader_script_crosslang_perf.md`, and completed `doc/05_design/compiler_loader_script_crosslang_perf.md` | Local/domain research, selected requirement/NFR docs with no lingering options, architecture, completed detail design | research/design owner | user selection + highest-capability reviewer |
| DOC-01 manual | Working admitted self-hosted docgen | `release/x86_64-unknown-linux-gnu/simple spipe-docgen test/05_perf/compiler_loader_script_crosslang_perf_spec.spl --output doc/06_spec --no-index` | Generated scenario sections, source hash/provenance, `0 stubs`, final readability review receipt | SPipe manual owner | highest-capability reviewer |
| VCS-01 | Intentional plan files committed; no tracked changes; separately owned GUI reports left untouched | `flock /tmp/simple-main-restart12-push.lock bash -c 'env -u GH_TOKEN -u GITHUB_TOKEN git fetch origin main && git rebase origin/main && env -u GH_TOKEN -u GITHUB_TOKEN git push origin HEAD:main && env -u GH_TOKEN -u GITHUB_TOKEN git fetch origin main && git merge-base --is-ancestor HEAD origin/main && git diff --quiet && git diff --cached --quiet'` followed by `git status --short` and, only after reachability succeeds, `printf '%s PASS\n' "$(git rev-parse HEAD)" > /tmp/restart12-compiler_perf_b.done` | Commit hash, fetch/rebase/push output, reachability exit 0, status showing only separately owned files, `/tmp/restart12-compiler_perf_b.done` | merge owner | highest-capability reviewer |

The implementation handoff remains WARN/BLOCKED, never verify PASS or release.
No unavailable row is excluded or converted to `skip()`.

## Evidence semantics

The canonical counter is at the `rt_file_exists` facade and counts failed
existence probes, not syscalls. Native C/Rust providers admit a lease before the
facade operation, stop accepting before draining, and use a non-wrapping 63-bit
generation. The pure-Simple interpreter provider is single-threaded and
fail-closed. Packed results require `failed <= total <= 0x7fffffff`; the direct
two-miss fixture requires `(total, failed) = (2, 2)` and must already be absent.

The retained byte lane requires GNU `/usr/bin/time` plus `timeout` on Linux,
validates semantic receipts before RSS, rejects payload RSS above four times
the payload, and keeps fixture timing separate from host p50/p95 wall samples.
Unsupported hosts remain unavailable.

## Cooperative review

- `/root/plan_evidence_audit` (`gpt-5.6-luna`, high), read-only evidence scope:
  found Stage 4 admission, packed coverage, traceability, and manual-provenance
  gaps; all findings were merged into the matrix and ledger.
- `/root/guide_wiki_audit` (`gpt-5.6-luna`, high), read-only knowledge scope:
  found stale completion language and incomplete manual status; all findings
  were merged into the guide/wiki/manual dispositions.
- Merge owner: root Codex session in this detached worktree.
- `/root/high_model_plan_review` (`gpt-5.6-sol`, xhigh), cycle 1: `REJECT`.
  Its taxonomy, exact-command, tracking, receipt, and completion-wording
  corrections are represented in this revision.
- The same reviewer, cycle 2: `REJECT` on four residual exactness gaps in layer
  wording, packed-boundary anchors, VCS-01 handoff, and interactive workflow
  invocation. All four were corrected.
- The same reviewer, cycle 3: `ACCEPT`. It accepted plan completeness and
  done-state honesty while feature/manual/research/design/live gates remain
  explicitly BLOCKED.
- Only the future generated-manual readability review remains assigned to the
  highest-capability reviewer after admitted docgen. The generated manual itself
  is BLOCKED; plan done-state review is accepted.

## Plan completion checklist

- [x] Scope and non-goals are explicit.
- [x] Every feature requirement surface has an acceptance row and owner.
- [x] Current evidence is separated from pending live verification.
- [x] Missing artifacts/helpers are called out instead of inferred.
- [x] Every blocker has a prerequisite, resume command, retained artifact,
  owner, and reviewer.
- [x] Manual step and checker vocabulary is frozen.
- [x] Lower-model audits are merged.
- [x] Guide/wiki and plan-facing manual summary/dispositions are updated; generated manual completion remains BLOCKED.
- [x] Highest-capability review accepts the merged plan.
- [ ] Focused plan-quality gates pass and intentional files are committed.

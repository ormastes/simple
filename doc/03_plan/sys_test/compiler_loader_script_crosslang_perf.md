# Compiler loader, script, and packed-byte performance plan

## Plan status

Plan content accepted at `3fdfa0d3351` and the current operational reconciliation
accepted by `/root/reconciled_plan_review`; `/root/final_nonstage4_review`
accepted the current Stage-4-excluded continuation on bounded review cycle 3.
The SimpleOS syscall extension commit
`aef64fb1951136fbb98521ce1a67643207752a26` was integrated under the lane lock
and proved reachable from refreshed `origin/main`. The later Stage-2 optimizer
and Stage-3 planner-localization evidence is integrated at
`30f4de92f04d9c7717db9c3678eaa9f1bd7b9334`, also reachable from refreshed
`origin/main`.
Feature verification remains blocked. This document is the canonical
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

Out of scope: substituting the Rust seed or Stage 2/3 diagnostics for Stage 4
evidence, claiming
filesystem syscall counts from facade counters, disabled-path assembly/cycle
claims, changing public byte-array semantics, or absorbing unrelated
GUI/web/2D files. Stage 4 construction, admission, and deployment resume after
Stage 3 admission.

## Authoritative artifacts

| Artifact | Path | Current disposition |
|---|---|---|
| SPipe state | `.spipe/compiler_loader_script_crosslang_perf/state.md` | Current planning acceptance and review contract |
| Executable SSpec | `test/05_perf/compiler_loader_script_crosslang_perf_spec.spl` | Present; declares REQ-001..008 and NFR-001..006 |
| Scenario manual | `doc/06_spec/05_perf/compiler_loader_script_crosslang_perf_spec.md` | Present summary with operator flow; generated scenario sections/hash/docgen provenance remain blocked |
| Local/domain research | `doc/01_research/{local,domain}/compiler_loader_script_crosslang_perf.md` | Present; domain synthesis awaits optional live-source refresh when the mandated context-mode fetcher is available |
| Requirement options | `doc/02_requirements/{feature,nfr}/compiler_loader_script_crosslang_perf_options.md` | Present; no option selected; explicit user choice is mandatory |
| Architecture | `doc/04_architecture/compiler_loader_script_crosslang_perf.md` | Decision-ready draft; acceptance waits for selected requirements |
| Detail design | `doc/05_design/compiler_loader_script_crosslang_perf.md` | Expanded for resolver/probe/RSS and packed storage/write-back/foreign capability; final acceptance waits for selected requirements |
| Compiler performance guide | `doc/07_guide/compiler/check_perf.md` | Must identify this plan and its blocked self-hosted lane |
| Feature expert | `doc/00_llm_process/feature_expert/compiler_loader_script_crosslang_perf/skill.md` | Required knowledge handoff |
| Compiler layer expert | `doc/00_llm_process/layer_expert/compiler_driver/skill.md` | Must link this lane |
| Loader blocker | `doc/08_tracking/bug/module_loader_negative_cache_stat_storm_2026-08-11.md` | Open verification condition retained |
| Packed-byte history | `doc/08_tracking/bug/interpreter_byte_array_len_widening_spin_2026-08-13.md` | Fixed historical boundary/performance defect |
| Packed-byte evidence gaps | `doc/08_tracking/bug/compiler_loader_packed_byte_evidence_gaps_2026-08-14.md` | PBL-01/02 closure and PBL-03 atomic cutover with an explicit macOS WARN |
| Packed-byte deliberate-red evidence | `doc/09_report/compiler_loader_packed_byte_deliberate_red_evidence_2026-08-14.md` | PBL-01/02 named status-101 failures and exact reversion receipts |
| Build11 Stage 3 blocker | `doc/08_tracking/bug/build11_stage3_compile_context_corruption_2026-08-14.md` | Open fresh-lane corruption frontier after a clean 603-file parse |
| Retained harness | `scripts/check/check-cross-language-perf.shs` | Present |
| C facade selfcheck | `scripts/check/check-file-exists-probe-c.shs` | Present |

## Build11 replacement lane A status (2026-08-14)

Fresh execution receipt: `r4` stopped before Stage 2 admission because the
formal-verification HIR consumer slice lacked its flat-AST contract producer.
That coherent parser/AST/constructor slice is restored. The next `r5`
source-frozen full bootstrap was the third and final fix cycle for this
session. It admitted Stage 2 (`858 compiled, 0 cached, 0 failed`; sanity pass;
SHA-256 `d2ed1d54673bc4cc848024ebbc229a873053dc315d8412613184bfdc5faec947`),
but Stage 3 produced no candidate while RSS grew to about 19.8 GiB over 143
seconds of single-core execution. It was terminated before host OOM. Stage 4,
deployment, and admission-dependent feature evidence remain BLOCKED. Before
another Stage-3 localization run, the next fresh session must repair the now
localized cross-registry argv ingress with private non-interposable pure-owner
helpers, prove it under the production link policy, and emit the mandatory
bootstrap receipt. Only then may it localize the remaining Stage-3 allocation
loop; the old receipt-less command must not be repeated.

Next-cycle localization identified a historical ownership regression: commit
`866559f16e0` made `ModuleSurfacesByName` reference-owned after proving that a
value boundary duplicated the full retained surface graph, but the restored
lineage had changed it back to a struct. The exact class invariant and a
source-contract regression are restored before the cache-preserving r5 Stage 3
resume; this is a distinct fix, not an unchanged rerun.

Continuation receipt: the class restoration and inline scalar lookup did not
change the early allocation slope. The third diagnostic ran the admitted Stage
2 executable under GDB and proved the live pre-HIR owner was recursive
flat-statement conversion of the 97-arm `char_to_ascii` elif table (60 bridge
frames at the later sample). The table is now an equivalent `char_code` range
check. Because that finding arrived on cycle three, its cache-preserving Stage
3 verification is the first action for the next session; Stage 4 and feature
evidence remain BLOCKED until it passes.

Latest verification receipt: a validated typed Stage 3 authorization was used,
but three bounded resumes still stopped at parse progress 128. The ASCII leaf
and the 41-arm expression dispatcher are no longer nested chains; closure
inventory nevertheless found eight additional 19..52-arm chains. The next
critical-path work is a systemic iterative if/elif representation in the flat
parser/bridge followed by a fresh Stage 2 rebuild. The admitted r5 executor is
frozen and cannot consume its own driver/parser implementation changes.

Stage 4 orchestration is independently MISSING: the current Stage 3 resume
exits after provenance admission, while the only `--deploy` path deletes and
rebuilds Stage 2/3. Implement the fail-closed continuation specified in
`doc/08_tracking/bug/stage4_resume_from_admitted_gap_2026-08-14.md` before
claiming that an admitted resumed Stage 3 can flow canonically to deployment.

This detached worktree is the fresh lane-A replacement. The previous Build11
candidate did not reach performance admission: its strict Stage 2 bootstrap
ended after about 52 minutes with 61 HIR field-inference failures (mostly
`struct 'ANY' field ...`), including `src/compiler/99.loader/module_loader.spl`.
Consequently there is no admissible self-hosted failed-probe, latency, or RSS
receipt from that attempt. Rust-seed measurements remain diagnostic only.

Current acceptance items, each to be verified once in this lane:

- [x] Establish the focused loader/performance baseline with the canonical
  self-hosted runtime and retain the exact failure or PASS receipt.
- [ ] Remove the remaining in-scope Build11 compiler/loader/script blocker
  without seed fallback, disabled checks, reduced workload, or fabricated
  evidence.
- [x] Run the optimizer audit on each touched `.spl` implementation file and
  address or explicitly disposition its findings.
- [x] Pass the independent C provider lifecycle/self-check gate with real assertions.
- [ ] Pass the focused SPipe performance specification with real assertions.
- [ ] Pass the compiler/core/lib and MCP/LSP checks required for compiler or
  library changes, including the core-runtime and MCP native smoke gates when
  the language/startup surface is affected.
- [x] Record admitted self-hosted failed-probe reduction, warm latency, and
  maximum RSS evidence, or retain a concrete WARN blocker if bootstrap remains
  independently blocked after at most three fix cycles.
- [x] Commit the lane-A implementation change, serialize integration with
  `/tmp/simple-main-restart12-push.lock`, rebase onto fetched `origin/main`, push
  detached `HEAD:main` without token environment overrides, and prove the
  pushed commit is reachable from a freshly fetched `origin/main`.
- [x] Finish lane A with a clean tree and only then write
  `/tmp/restart12-compiler_perf_a.done` as `<commit> PASS` or `<commit> WARN`.
  Prior integration receipt: `56448da2b25bbe90523ad672b25db2abaef74a67 WARN`, reachable
  from refreshed `origin/main`. The tracked/lane-owned tree was clean; two
  unrelated GUI report files remained untracked and excluded.

Known blocker at lane start: prior Build11 Stage 2 could not type the compiler
tree, so the admitted performance rows are pending. This lane first determines
whether current `origin/main` already contains the upstream compiler repairs;
if not, it fixes the narrow root cause rather than annotating 61 call sites.

Acceptance accounting: the canonical deployed baseline was retained as status
139 in `rt_env_set`; the independent C lifecycle/self-check half passed. The
Stage 2/parser blocker was removed, while the focused SPipe half remains open
because no admitted Stage 3 deployment exists. The WARN alternative for the
performance rows is satisfied by the concrete tracking record named below.

Fix-cycle 1 result: current main cleared Stage 2 (`845 compiled, 0 cached, 0
failed`), so the inherited 61-file blocker is resolved upstream. Stage 3 then
failed at `typed_storage_view_producer.spl:132` because its self-host parser
requires parentheses around a multiline boolean condition. Lane A added those
grammar-required parentheses without changing the predicate; the admitted
resume must now pass Stage 3 before any performance row can be credited.

Fix-cycle 2 result: Stage 2 again passed (`845 compiled, 0 failed`), and Stage
3 parsed all 603 files with zero failures, proving the multiline grammar fix.
It then segfaulted at the first HIR-loop dispatch to
`CompileContext.error_count()`; GDB resolved the top frame to that getter and
the following diagnostic never printed. The final cycle replaces fragile
getter dispatch in this staged hot path with direct reads of its typed
`error_count_value` scalar. This is behavior-preserving and keeps all mutation
inside `CompileContext.add_error`.

Fix-cycle 3 result: the admitted Stage 2 recovery again parsed all 603 files
with zero failures but exited 139 before the first HIR progress row. Direct
scalar access did not clear the corruption, so that unproven workaround was
removed. The bounded lane stops here per the three-cycle cap. The grammar fix
remains because it is independently proven by both later cycles. Admitted
self-hosted loader probe/latency/RSS rows and deployed focused SPipe execution
remain WARN-blocked by the Stage 3 context corruption. The later reduced-entry
Stage-2 optimizer audit supersedes the historical optimizer blocker.

Artifact gaps are explicit: local/domain research, option sets, a decision-ready
architecture draft, an agent-task breakdown, and expanded detail design now
exist. Selected feature and NFR requirements remain **MISSING** until the user
chooses one option from each set; architecture/design acceptance and formal
`@req` traceability wait for that choice. The manual still lacks admitted
self-hosted docgen provenance.

### Lane-B fresh Stage 2 -> Stage 3 handoff

The fresh lane-B source-frozen bootstrap used the canonical cache-preserving
`--full-bootstrap --deploy` command. Cycle 1 stopped in Stage 2 because the
retained-contract HIR declarations/producers had been partially removed while
MIR/Lean consumers remained. The current upstream reconciliation contains the
complete producer and resolver behavior; this lane retains only compatible
consumer typing and the shared HIR declarations where not already present.

Cycle 2 admitted Stage 2 and entered Stage 3, then rejected fourteen backend
module constants whose bare-zero initializer could not safely determine a MIR
type. The CUDA/ELF/Mach-O/x86/AArch64 zero constants now carry explicit `i64`
annotations. Cycle 3 admitted Stage 2 again and cleared all fourteen errors,
but Stage 3 received an external SIGTERM (exit 143) after source indices 0..2.
The canonical wrapper has no Stage 3 timeout. A fresh long-lived resume proved
the process stayed CPU-bound while RSS grew from about 7.4 GiB to 20 GiB after
source 2 `post-store`, without marker or I/O progress. The localized owner is
aggregate-by-value linear surface lookup; the current repair uses scalar
name/index lookup first and a scalar-prefiltered physical-identity fallback.
No Stage 3 candidate, Stage 4 deployment, or live performance row exists yet.

Four fixed-string, context-free `dtrace` canaries mark lowering entry, source
map completion, and the before/after module-surface boundary. They are enabled
only with `SIMPLE_INTERP_TRACE=1` and are diagnostic, not acceptance evidence.

## Acceptance matrix

REQ/NFR identifiers below are provisional identifiers declared by the executable
spec. They become formal traceability only after the mandatory research and user
selection flow produces the missing selected requirement documents.

| ID | Provisional requirement coverage | Acceptance condition | Authoritative evidence | Current state |
|---|---|---|---|---|
| PBL-01 | REQ-008, NFR-003 | Index, slice, iteration, concat, clone, equality, freeze, and byte-valued mutation preserve packed storage; non-byte insertion widens once | Green focused tests plus `doc/09_report/compiler_loader_packed_byte_deliberate_red_evidence_2026-08-14.md` | PROVED at Rust interpreter boundary — final suites pass 4/4, 1/1 representation concat, and 4/4 identifier cases; named deliberate-red fails status 101 and is reverted |
| PBL-02 | REQ-008, NFR-003 | Identifier and projected-place mutators write back, preserve COW aliases, return removed elements, reject immutable/frozen receivers | Green focused tests plus `doc/09_report/compiler_loader_packed_byte_deliberate_red_evidence_2026-08-14.md` | PROVED at Rust interpreter boundary — final identifier cases pass 4/4 and projected-place write-back 1/1; named deliberate-red fails status 101 and is reverted |
| PBL-03 | REQ-008, NFR-003/006 | Foreign packed-byte pointers are input-only, descriptor-bounded, nested adapters are scoped, and capabilities cannot escape a call | Production foreign-dispatch route plus compile-fail/equivalent escape enforcement | PROVED WITH TARGET WARN — the original Rust/native route is proved. The refreshed-origin SimpleOS extension is source/ABI/provider-contract proved: typed callers, production RuntimeValue decoding, atomic readback, bounds/cleanup tests, and zero positive old-symbol references. A real SimpleOS target archive/link/runtime and real macOS Metal compile remain unproved; no Stage-4 claim |
| LDR-01 | REQ-004/005/006/007, NFR-002 | Exact repeated miss caches once; adjacent callers remain distinct; reset invalidates; resolution result is unchanged | Focused SSpec and resolver unit coverage | BLOCKED — implementation is present; fresh admitted self-hosted execution is unavailable |
| LDR-02 | REQ-004/005, NFR-001/002/006 | 100 reset-per-request resolutions versus 1000 retained requests produce identical results, uncached counts 100/1, positive failed-probe baseline, and cached probes at most 10% | SSpec plus C facade selfcheck | BLOCKED — contracts are present; fresh admitted self-hosted measurement is unavailable |
| PRV-01 | REQ-001/003, NFR-005 | Exact executable path/hash and actual mode are admitted; seed, stale hash, requested/actual mismatch, and fallback are rejected before timing | SSpec and retained harness contract tests | CONTRADICTED — the deployed candidate exists but exit 139 on its test/help ABI path disproves admission |
| BYT-01 | REQ-001/002/008, NFR-003/004 | Native byte fixture validates 1/4/32 MiB length, boundaries, checksum, fixture timing, and RSS at no more than four times payload before admitting a row | SSpec, retained byte contract, and cross-language harness | BLOCKED — contract exists; live retained row requires an admitted candidate |
| XLG-01 | REQ-001/002, NFR-004 | C/Rust/Go/Python/Bun/Simple workloads have equivalent checksums, including `fib(35)=9227465`; unavailable peers remain unavailable | Retained schema/provenance/byte contract scripts | BLOCKED — contracts exist; fresh report requires an admitted candidate |
| CMP-01 | REQ-007, NFR-001/005/006 | Self-hosted compiler checks for `src/compiler`, `src/lib`, MCP, LSP, and MCP stdio smoke pass without seed fallback | Commands below | BLOCKED — deployed candidate exists but is not admitted |
| PLN-01 | all | Canonical plan, guide, expert knowledge, blockers, and cooperative-review receipts are internally consistent and pass focused document gates | Document review and layout guard | PROVED — review accepted; SPipe wiring, spec-layout, and working/staged runtime guards pass. Global workspace-root strict audit remains WARN-blocked by 137 pre-existing unrelated manifest violations |
| DOC-01 | all | Selected research/requirements, accepted architecture/detail design, and generated manual provenance exist | Artifact review and admitted docgen | BLOCKED — research/options/drafts now exist; user selection and post-selection acceptance remain outstanding. One Stage-2 docgen attempt failed immediately with `unknown command 'spipe-docgen'`; admitted docgen remains Phase-4-dependent |
| VCS-01 | all | Only intentional lane-A files are committed; locked integration reaches refreshed `origin/main`; tree and lane marker are truthful | Git receipts | PROVED through `30f4de92f04d9c7717db9c3678eaa9f1bd7b9334`; final bookkeeping follows the same locked sequence and unrelated untracked GUI reports are excluded |

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
   The post-integration SimpleOS extension has these independent one-pass gates:
   `cc -std=c11 -Wall -Wextra -Werror -Isrc/runtime src/runtime/runtime_simpleos_syscall_adapters.c test/01_unit/runtime/simpleos_syscall_byte_adapters_test.c -o /tmp/restart12-simpleos-syscall-adapters-test && /tmp/restart12-simpleos-syscall-adapters-test`;
   `cc -std=c11 -D_GNU_SOURCE -O0 -ffunction-sections -fdata-sections -Isrc/runtime src/runtime/runtime_native.c src/runtime/runtime_simpleos_syscall_adapters.c test/01_unit/runtime/simpleos_syscall_byte_adapters_runtime_test.c -Wl,--gc-sections -lm -ldl -lpthread -o /tmp/restart12-simpleos-syscall-runtime-test && /tmp/restart12-simpleos-syscall-runtime-test`;
   `cargo test -p simple-compiler simpleos_syscall --lib` and
   `cargo test -p simple-runtime-abi simpleos_syscall_byte_adapters_are_codegen_visible --lib`
   from `src/compiler_rust`; and
   `rg -n 'rt_array_data_ptr_u8' --glob '!doc/**' .`, whose results must all be
   explicit negative assertions. Stage-2 compile-only evidence uses the exact
   source-contract native-build command retained in the packed-byte tracking
   record. The selected-owner test builds the pure-Simple archive with
   `SIMPLE_BINARY="$PWD/build/restart12-build11-a-r2/output/stage2/x86_64-unknown-linux-gnu/simple" SIMPLE_CORE_BACKEND=cranelift sh scripts/os/simpleos-core-archive.shs --target x86_64-unknown-linux-gnu --out-dir /tmp/restart12-simple-core-owner --backend cranelift`,
   then links/runs
   `cc -std=c11 -D_GNU_SOURCE -O0 -ffunction-sections -fdata-sections -Isrc/runtime src/runtime/runtime_simpleos_syscall_adapters.c test/01_unit/runtime/simpleos_syscall_byte_adapters_runtime_test.c /tmp/restart12-simple-core-owner/libsimple_runtime.a -Wl,--gc-sections -lm -ldl -lpthread -o /tmp/restart12-simpleos-syscall-simple-core-test && /tmp/restart12-simpleos-syscall-simple-core-test`.
   Actual SimpleOS-target archive/link/runtime proof remains WARN rather than
   inferred.
4. Resolver/facade evidence: the C selfcheck is independent and may run once
   even when Stage 4 admission fails: `sh scripts/check/check-file-exists-probe-c.shs`.
   The following SPipe command is admission-dependent and must stop after a
   failed step 1:
   `release/x86_64-unknown-linux-gnu/simple test test/05_perf/compiler_loader_script_crosslang_perf_spec.spl
   --mode=interpreter --no-session-daemon` and require the authoritative file
   verdict with no dropped examples.
5. Retained harness source contracts may run once independently:
   `sh test/05_perf/profile_scripts/cross_language_compile_failure_contract_test.shs`;
   `sh test/05_perf/profile_scripts/cross_language_compiler_provenance_contract_test.shs`;
   `sh test/05_perf/profile_scripts/cross_language_byte_retained_contract_test.shs`;
   `sh test/05_perf/profile_scripts/cross_language_retained_schema_contract_test.shs`;
   The live harness is admission-dependent and must stop after a failed step 1:
   `RUN_TIMEOUT=30 SIMPLE_BINARY="$PWD/release/x86_64-unknown-linux-gnu/simple" REPORT_PATH="$PWD/build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf/cross_language_perf.md" sh scripts/check/check-cross-language-perf.shs`.
6. Compiler/tool-server surface (entirely admission-dependent; stop after a
   failed step 1):
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

The distinct Stage-2 optimizer audit is retained in
`doc/09_report/compiler_loader_stage2_optimizer_audit_2026-08-14.md`. Its real
`optimize_full_analyze` entry closure built 55 files with zero failures and
analyzed all four touched `.spl` files once; all findings were explicitly
dispositioned without an unsafe source rewrite. Future `.spl` changes require
a fresh audit and correctness/performance comparison.

## Blocker and resume ledger

| Blocked IDs | Missing prerequisite | Exact resume command | Retained artifacts | Owner | Final reviewer |
|---|---|---|---|---|---|
| PBL-03 platform WARN | Compile the scoped Metal metallib adapter on a real Apple toolchain | `cd src/compiler_rust && cargo check -p simple-runtime --target aarch64-apple-darwin` on macOS with the Apple SDK/toolchain | macOS compile log plus existing scoped-call and removed-symbol receipts | runtime SFFI owner | highest-capability reviewer |
| LDR-01/02, PRV-01, BYT-01, XLG-01, CMP-01 | Repair/redeploy an admitted self-hosted Stage 4 CLI per the linked repair plan/TODO | `test -x release/x86_64-unknown-linux-gnu/simple && release/x86_64-unknown-linux-gnu/simple --version && release/x86_64-unknown-linux-gnu/simple test --help && sh scripts/check/check-file-exists-probe-c.shs && release/x86_64-unknown-linux-gnu/simple test test/05_perf/compiler_loader_script_crosslang_perf_spec.spl --mode=interpreter --no-session-daemon && RUN_TIMEOUT=30 SIMPLE_BINARY="$PWD/release/x86_64-unknown-linux-gnu/simple" REPORT_PATH="$PWD/build/test-artifacts/05_perf/compiler_loader_script_crosslang_perf/cross_language_perf.md" sh scripts/check/check-cross-language-perf.shs && release/x86_64-unknown-linux-gnu/simple check src/compiler && release/x86_64-unknown-linux-gnu/simple check src/lib && release/x86_64-unknown-linux-gnu/simple check src/app/mcp && release/x86_64-unknown-linux-gnu/simple check src/app/simple_lsp_mcp && SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test test/02_integration/app/mcp_stdio_integration_spec.spl --mode=interpreter` | Binary path/hash, version/help logs, checker/spec logs, retained profile report, RSS receipts | compiler-loader performance owner | highest-capability reviewer |
| LDR-01/02, PRV-01, BYT-01, XLG-01, CMP-01 — Build11 prerequisite | Admit/prove `rt_native_eq` (or an equivalent fail-closed comparison already supported by the pure runtime closure), then reapply the private non-interposable argv-owner bridge and pass the populated registry-sensitive production-link test; rebuild the CLI and produce the mandatory receipt; finally run one source-frozen debugger-backed Stage-3 diagnostic cycle | First run `<current capable pure-Simple CLI> build bootstrap --bootstrap-reason=self-host-convergence-check --bootstrap-receipt=$PWD/build/restart12-build11-a-r3/reason.receipt`; only after that succeeds run `env BOOTSTRAP_NATIVE_CACHE_TTL_DAYS=0 SIMPLE_NO_STUB_FALLBACK=1 sh scripts/bootstrap/bootstrap-from-scratch.sh --bootstrap-receipt="$PWD/build/restart12-build11-a-r3/reason.receipt" --full-bootstrap --deploy --backend=cranelift --output=build/restart12-build11-a-r3/output` | Undefined-`rt_native_eq` relocation/disassembly receipt, populated registry-sensitive whole-archive test, planner-produced receipt, Stage 2/3 logs and provenance manifests, candidate hash | pure-Simple compiler-driver owner | highest-capability reviewer |
| DOC-01 traceability | Explicit user choice from the present feature/NFR option sets, then post-selection architecture/design acceptance | Delete unchosen options; write `doc/02_requirements/feature/compiler_loader_script_crosslang_perf.md` and `doc/02_requirements/nfr/compiler_loader_script_crosslang_perf.md`; reconcile and accept the existing architecture/detail design | Selected requirement/NFR docs with no lingering options, accepted architecture and detail design | research/design owner | user selection + highest-capability reviewer |
| DOC-01 manual | Working admitted self-hosted docgen | `release/x86_64-unknown-linux-gnu/simple spipe-docgen test/05_perf/compiler_loader_script_crosslang_perf_spec.spl --output doc/06_spec --no-index` | Generated scenario sections, source hash/provenance, `0 stubs`, final readability review receipt | SPipe manual owner | highest-capability reviewer |
| VCS-01 reconciliation | Intentional plan files committed; no tracked changes; separately owned files untouched | `flock /tmp/simple-main-restart12-push.lock bash -c 'env -u GH_TOKEN -u GITHUB_TOKEN git fetch origin main && git rebase origin/main && env -u GH_TOKEN -u GITHUB_TOKEN git push origin HEAD:main && env -u GH_TOKEN -u GITHUB_TOKEN git fetch origin main && git merge-base --is-ancestor HEAD origin/main && git diff --quiet && git diff --cached --quiet'` followed by `git status --short` and, only after reachability succeeds, `printf '%s WARN\n' "$(git rev-parse HEAD)" > /tmp/restart12-compiler_perf_a.done` | Commit hash, fetch/rebase/push output, reachability exit 0, clean status, updated lane-A WARN marker | merge owner | highest-capability reviewer |

The implementation handoff remains WARN/BLOCKED, never verify PASS or release.
No unavailable row is excluded or converted to `skip()`.

## Evidence semantics

### Host matrix

| Host | Disposition |
|---|---|
| Linux with GNU `/usr/bin/time` and `timeout` | Runnable after candidate admission; retain OS/kernel/CPU/memory/tool versions with every sample |
| macOS, FreeBSD, Windows, or Linux without GNU time or `timeout` | UNAVAILABLE until a host-specific command and equivalent RSS/timing contract are selected and reviewed |

Never aggregate or compare samples collected on different hosts as one
performance row. Cross-host results remain separate capability rows.

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

The receipts below through cycle 3 are historical and bind revision
`3fdfa0d3351`. The present reconciliation has fresh parallel audits from
`/root/traceability_audit` and `/root/operator_audit`; their findings are merged
here and require a new higher-capability acceptance receipt before `PLN-01` is
proved. `/root/command_receipt_check` accepted all new commands and receipts;
`/root/status_consistency_check` found one stale historical statement, which was
corrected; `/root/reconciled_plan_review` (`gpt-5.6-sol`, high) then returned
`ACCEPT` after the Linux host row was made consistent with the GNU time plus
`timeout` requirement.

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
- `/root/final_nonstage4_review`, current Stage-4-excluded continuation, cycles
  1-2: `REJECT` on missing deliberate-red receipts and stale/factually
  inconsistent dispositions. All findings were corrected without weakening
  the evidence contract.
- The same reviewer, cycle 3: `ACCEPT`. At that reviewed revision PBL-01/02
  remained honestly BLOCKED on missing red receipts despite green tests. The
  later receipt session supersedes that historical disposition and proves both
  at the Rust interpreter boundary; at that revision PBL-03, selection/manual, Stage 3, and
  deployed-CLI blockers remain explicit, with no Stage 2/3 substitution for
  Stage 4.
- At historical revision `3fdfa0d3351`, only the future generated-manual
  readability review remained assigned after admitted docgen. The generated
  manual remains BLOCKED; the fresh cycle-3 receipt accepted the current
  Stage-4-excluded done-state honesty.
- `/root/receipt_reconcile_review`, receipt/PBL-03 reconciliation cycle 1:
  `REJECT` on stale historical PBL and premature current-VCS wording. All
  findings were corrected without broadening the evidence claims.
- The same reviewer, cycle 2: `ACCEPT`. PBL-01/02 are proved only at the Rust
  interpreter boundary, and at that revision PBL-03 remained open with an atomic migration contract,
  Stage 4 remains excluded, and current VCS integration is operationally
  pending as recorded below.
- `/root/pbl03c_review`, cycle 1: `ACCEPT`. It independently confirmed bounded
  HashSet indexing/clear, unchanged asymptotic complexity, non-vacuous focused
  coverage, the 8-owner/23-use/1-stored-address live inventory, absence of the
  reverted PBL-03A/B prototypes, and the compile-only Stage-2 evidence limit.
- The same reviewer, narrow cycle 2: `ACCEPT` on the historical single
  180-second Stage-2 optimizer-build timeout. The later reduced-entry audit
  supersedes that optimizer-audit blocker without claiming performance proof.
- `/root/pbl03_atomic_review`, atomic merge cycles 1-2: cycle 1 `REJECT` found
  three clone-and-discard interpreter Vulkan readback handlers; they were
  removed and kept native/JIT-only. Cycle 2 `ACCEPT` found no merge blocker and
  retained a real-macOS compile WARN after the Linux cross-check stopped in the
  host C toolchain before compiling this crate.

## Plan completion checklist

- [x] Scope and non-goals are explicit.
- [x] Every provisional spec requirement surface has an acceptance row; blocked
  ownership is supplied by the matching ledger row.
- [x] Current evidence is separated from pending live verification.
- [x] Missing artifacts/helpers are called out instead of inferred.
- [x] Every blocker has a prerequisite, resume command, retained artifact,
  owner, and reviewer.
- [x] Manual step and checker vocabulary is frozen.
- [x] Lower-model audits are merged.
- [x] Guide/wiki and plan-facing manual summary/dispositions are updated; generated manual completion remains BLOCKED.
- [x] Fresh highest-capability review accepts this Stage-4-excluded continuation.
- [x] Focused plan-quality gates pass; the global workspace-root strict audit
  truthfully remains WARN with 137 pre-existing unrelated manifest violations.
- [x] The post-integration SimpleOS PBL-03 extension is committed at
  `aef64fb1951136fbb98521ce1a67643207752a26`, integrated through the lane lock,
  and reachable from refreshed `origin/main`. Final bookkeeping and the WARN
  marker follow the same locked sequence; unrelated GUI reports are excluded.

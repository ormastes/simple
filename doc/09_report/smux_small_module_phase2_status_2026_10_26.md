# Small-module Phase 2 implementation status

The user requested Astra implementation in smaller modules and interim Phase 2 execution. The existing accepted CoreMux/Caret/IDE scope is unchanged. This work does not establish that smux replaces tmux or that either backend meets the N2 system requirements.

The implementation guide is [the small-module task breakdown](../03_plan/agent_tasks/smux_small_module_phase2_2026_10_26.md). Separate Astra authors own exact-target resolution, bounded per-lease events and scoped metadata queries; separate Astra reviewers inspect each source/spec/manual slice. Root owns integration and execution. These pure modules do not independently implement the authenticated transport dispatcher or migrate every consumer.

## Source candidates

| Module | Authored cases | Execution |
|---|---:|---|
| Exact-target resolver | 18 | NOT_RUN |
| Bounded per-lease event journal | 10 | NOT_RUN |
| Scoped metadata/current-context queries | 18 | NOT_RUN |

These 46 authored cases are not passing-case counts. Exact source freezes and independent review artifacts are retained under `build/review/`; reviewed source status must remain distinct from runtime qualification.

Independent event review identified a P2 allocation/cardinality defect: an unchecked array push could advance a returned cursor without carrying the event. Event source cycle 3 adds construction/cardinality guards; independent Astra review closed that bounded source finding. Review confirmed the same concrete configured-container behavior affects resolver candidate collection (P2, lost ambiguity) and metadata projection (P1, a partial graph returned as complete). Resolver cycle 2 and metadata cycle 2 also passed scoped independent source review. Prior receipts and findings are preserved. The metadata reviewer traced both array and dictionary failure behavior to the configured container owners; this is source-derived evidence, not an executed allocation-failure test. Local guards do not qualify allocation-failure behavior inside shared validators or replace runtime fault testing.

## Execution admission

The [finite execution plan](../03_plan/sys_test/smux_small_module_phase2_execution_2026_10_26.md) uses the immutable Phase 2 compiler SHA256 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`. The tracked canonical wrapper generator is `test/fixtures/test_runner/native_framework/generate_controls.spl`. It calls the production wrapper and lexer facts; it is not an assertion-framework replacement.

Actual new SSpec cases executed: **0**. No feature, profile or release PASS is claimed. After the other compiler tree exited, H0 actually ran and failed with native exit 1. All 96 selected HIR modules lowered; 25 MIR modules failed, with 211 failure records. Linking was skipped, zero objects were admitted, and no executable was produced. Peak process-tree RSS was 3,284,216 KiB, within the enforcing 5,859,375 KiB bound. This was a compiler failure, not a timeout or memory-limit failure.

Independent Astra diagnosis grouped all 211 manifest rows into 91 ambiguous imported provider-owner errors and 120 duplicate imported-global errors (four token-constant rows and 116 AST-expression constant rows). `compiler.core.*` and `compiler.frontend.core.*` resolve to the same physical sources. The production lexer itself mixes these spellings, so merely renaming the driver's import is not a justified repair. No independent file-IO, wrapper-signature, allocator or syntax failure was identified in this manifest. This does not prove that later compilation or execution would succeed. No unchanged retry was run. The canonical wrapper and framework have not been replaced with another scanner or assertion implementation.

Current pure-Simple compiler source contains a relevant checked physical-provider alias coalescing path in `src/compiler/80.driver/driver_mir_provider_aliases.spl`, called from MIR-feed lowering. This is a source repair candidate, not evidence that the immutable Phase 2 executable contains or correctly executes it. Historical prepared alias-materialization receipts do not authorize another build: their source-readiness record says `compiler_launched: false` and `UNKNOWN_EXCEPTION_NOT_GRANTED`. No Phase 2 rebuild or unadmitted materialization retry was performed.

Terminal artifacts: `build/review/phase2-smux-framework-driver-1/compile.log`, `compile.receipt`, `memory.env`, `runtime-pins.sdn`, `invocation.sdn`, and `smux_framework_driver.exe.go-to-end.sdn`. Bounded compile log SHA256: `b3e4ab390c8d214c58adc76b3702bbff13d8e7e2f4778aad03318fd7695753b2`. The native receipt records child-exit 1 and cleanup not needed. Runtime source/container pins remain separate from runtime feature qualification.

The first H0 supervisor setup failed before compiler launch because the reused Python source contained a UTF-8 BOM. The prepared supervisor now decodes that source with `utf-8-sig`; this correction has not itself been executed. The compiler workload has not started.

The host initially showed another session's active Phase 2 compiler tree, root PID 58224 and worker PID 996, targeting `C:/dev/simple-full-objects-release-20261026/attempt1/output/full-bootstrap.o` with 24 threads. Worker working set grew from approximately 20,506 MiB to 21,253 MiB at the post-module-freeze admission check. Our build was deferred under the one-heavy-compiler rule. At the final source-freeze admission check both other processes had exited, allowing H0 to launch with its own enforcing 5,859,375 KiB/180-second limits. No process belonging to the other session was changed or stopped. Private setup evidence is retained at `build/review/phase2-smux-framework-h0-status.sdn`.

After the host is available, H0 must generate the canonical wrappers; H1 must execute three passing examples; H2 must execute three examples with two passes and one genuine intentional failure, exit 1, including sibling continuation and hooks. Only then may the module rows execute. Generated files, discovery, compilation and zero-case summaries do not satisfy these gates.

This producer rejects `--library-mode`. Supported legacy-profile functional execution must be labelled separately and cannot certify configured NoGC selection. Historical harness failures remain in the execution plan; changing directories does not reset their attempt ledger. The exhausted cache-generator series is not retried by this cohort.

## Remaining gates

Source reviews, actual module SSpec, authenticated owner/transport composition, consumer migrations, real Windows terminal/process system tests and cleanup, both-backend N2, explicit profile qualification and formal-cache source-binding remain separate qualification gates. PR #4882 has already merged. The user subsequently instructed “just land your fixes”; the remaining source changes are being submitted separately on the current `release/1.0.0` base with this failed-execution evidence intact. Landing source does not qualify the product or convert any NOT_RUN result into PASS.

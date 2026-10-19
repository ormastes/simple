# Phase3 retains more than83GiB before MIR completion

Date:2026-10-17
Bug:BUG-PHASE3-MIR-RETAINED-MEMORY-20261017
Database registration:pending; no admitted database tool available.
Status:actual resource-limit failure; dominant retained owner and any leak remain unproven.

## Immutable reproduction evidence

Frozen source15f7ca45871b1250abf44c91efb6004625035035; producer0015C3FE0DFD28C22E55CBE488636F30E5BAA869D1608CAD4847685B9C553429 (exact0b7d87d9e0f source plus diagnostics-only patch). The executed producer used the checked C1 runtime: runtime_native.c SHA2561fdf03b16d1cf6fc0221a91aa463b9a4996b46620a46271561e81ab9b8f1a95f, checked27-object archive SHA2569D3FC63EBDF62EBD0F42164E17CBFCF546CCC7119FC065431E5DCFA29C36F89C, and genuine pow provider SHA2566C074A3B4F6CD195A03E6161196C9010937D488203C62AABFD620BA7475A073D; see the [producer link receipt](C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase2-value-diagnostic-producer-exception-20261017/strict-link/strict-link-proposal.json). Separately, the target runtime_native.c input SHA25646e61d85fdced2eb0821f21efadc12ad49539feaeb6f62df199ab1b5e37bbe08 and its [38-TU/73-file header manifest](C:/dev/simple-bootstrap-storage/phase3-validation-20261016/remote-review-3078-20261017/runtime-header-closure-receipt.json) were prepared for the compiler being built; they were not the producer's executed runtime and were not built into a target binary in this attempt. Canonical six source roots, bootstrap_main entry closure, Windows x86_64 MSVC/LLVM, core-c-bootstrap, requested80jobs with memory clamps. Final feature attempt3/3. No fourth attempt is authorized by this report.

The authoritative resource guard terminated with status rss-cap-exceeded, exit88, quiescent1. Peak RSS87,035,728KiB exceeded87,031,808KiB (83GiB) by3,920KiB; separately peak jobcommit90,112,932KiB. Worker14032 and coordinator20048 were gone. root_exit_raw0 in the receipt does not override the guard failure.

The HIR queue records1301PASS,0failed,0unfinished across16workers, including the repaired RT and AST payload modules. Retained ice_breadcrumbs.14032.log has1188mir_lower starts,1187done boundaries and no fail records. Lastdone compiler.backend.linker.elf.merge_strings; unmatchedlaststart compiler.backend.linker.elf.reloc_scan. A done boundary means its lowering call returned, not semantic PASS. Final mono PASS, aggregate MIR PASS and absence of accumulated fatal diagnostics are not proven by these artifacts. The buffered main log ends after HIR and does not negate the actual MIR breadcrumbs.

A single bounded inspection found0 native .o/.obj/.a/.lib/.exe artifacts in this attempt phase3/tmp and sameproducer cache. No link result is established. Historical objects from other producers are excluded.

External evidence: [terminal receipt](C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase3-0015-ast-payload-fixed-20261017/terminal-failure-analysis/terminal-evidence-receipt.json), [terminal report](C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase3-0015-ast-payload-fixed-20261017/terminal-failure-analysis/report.md), and [input hashes](C:/dev/simple-bootstrap-storage/phase3-validation-20261016/phase3-0015-ast-payload-fixed-20261017/terminal-failure-analysis/terminal-input-hashes.json) pin the observations and preserved breadcrumb stream. Original guard/HIR receipts, source snapshot, commands and all cache entries remain intact.

## Source-owned lifetime analysis

Exact baked0b driver_pipeline_lowering998 calls lower_module_transient_scoped;1048 retains each returned MirModule in ctx.mir_modules until later backend stages. The complete HIR/provider inventory remains available through the loop. This intentionally retains output graphs and can scale with module count even when scratch reclamation works.

module_lowering1759+ falls back to unscoped lowering if transient_array_scope_begin_v1 refuses. When a scope succeeds, it already resets function-local tracking before pausing, promotes the genuine lowered module and the explicit lowering-owner escape roots, promotes bootstrap registries, seals/publishes reverse references, and ends the scope. transient_owner.spl enumerates cross-module roots because their parent carriers may predate the scope. Removing these roots without consumer-lifetime proof risks use-after-free or lost declaration metadata. No safe redundant root clear has been established; this report implements none.

The last module is a position marker, not proof it caused the growth. No heap attachment, allocation profile, scope-refusal count or retained-byte census was captured. RSS alone cannot distinguish necessary output retention, duplicate promoted graphs, fallback scratch retention or allocator overhead. Remote probe-cap/nilskip changes are not proven memory remedies.

## Bounded instrumentation proposal, UNAPPLIED

Add env-gated scalar counters at the existing per-module transient owner boundary: scope begin accepted/refused, pause success, each promotion stage success/failure, scope end success/failure. Record a module ordinal and existing canonical module name, with no new graph serialization or repeated whole-closure traversal. Aggregate counters and emit one bounded record per existing64-module progress interval plus terminal. Instrument the existing decisions once; never invoke begin/promote/end a second time to measure them.

At the authoritative driver commit boundary, maintain incremental counts of completed modules/functions/blocks/instructions from the newly returned module only, before storing it. These are graph cardinalities, not retained bytes. Use existing typed MIR declarations; do not infer heap bytes from object layout or add an unowned FFI heap scanner. Any full retained-size measurement requires a separately designed runtime owner API and native qualification. Logging must stay off by default and counters must not affect admission/control flow.

Controls must compare diagnostics, MIR identities and genuine output between instrumentationoff/on for successful and failed modules; force or simulate scope-refusal only through an existing legitimate owner seam if one exists, otherwise mark that branch unexecuted. Verify end/abort outcomes and no publication of unpromoted graphs on every failure. Run no repeated green fullcompiler builds to qualify counters.

A semantic memory repair requires evidence assigning dominant ownership first. Candidate strategies include releasing proven-dead HIR only after all consumers finish, or persisting fully verified MIR/output under an admitted capsule and dependency-safe staged codegen. Neither is implemented here. Required modules and checks must remain present, aggregate failure must block linking, and no nilskip, stamp rewrite or smaller-context object graft may substitute for correct lifetime management.

## Qualification limits

Documentation/source analysis only. No runtime/compiler source changed; no build, debugger attachment or cache mutation performed by this lane. Existing native bootstrap3/3 limit remains exhausted. Broader compiler/lib/MCP/LSP checks and release admission remain UNRUN.

## Repair: dependency-safe staged native codegen (2026-10-19, UNQUALIFIED)

The native executable lane now flushes every full batch of `SIMPLE_NATIVE_STAGED_CODEGEN_BATCH` lowered modules (default `0` = off since review S1/S2: eviction reclaims nothing without a collector, so this is an opt-in diagnostic, not the memory fix; malformed fails closed) through mir_verify, borrow_check, optimize_mir, weave_aop, debug_trace and object emission, then releases that batch's MirModules (`driver_build/native_staged_codegen.spl`, `CompilerDriver.native_staged_codegen_flush_v1`). Every post-lowering consumer on this lane is per-module; the link reads object paths only. Cross-batch state is a summary: object paths, outcomes (failures still block the final link), collection bindings, lane/cache counters, witness-shadow and Phase-2 ledger evidence, and the whole schedule's names for the frozen storage registry. The tail batch takes the unchanged aot_compile chain and final compile_to_native verdict/link. Grouped, entry-object, SMF/self-contained/both, demand, full-inventory, bootstrap-flat and non-native backends stay unstaged. Not yet measured on a real phase 3; MirLowering-internal retention (transient-scope escape roots, bootstrap flat registries) is not released by this change. The `--low-memory` SEGV at MIR module 465 is a separate, unchased defect.

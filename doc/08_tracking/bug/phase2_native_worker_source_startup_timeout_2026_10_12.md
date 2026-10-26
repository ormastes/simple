# Phase2 native worker source startup exceeds bounded compiler build

Date:2026-10-12. Status: OPEN, observed diagnostic timeout; database insertion pending because no qualified bug database tool was invoked.

The retained immutable Phase2 producer f2ce31b4e4dea1ea6ca3e8726cd411144914c24ffcf58722021f38c4b6393dec cannot reach a native object in the900-second bounded successor build of committed source40ec45ca95e5b899983ece4d4ad8b17dfa35958d. This blocks embedding already committed HIR physical source identity, generic owner and omitted slice-end repairs needed by the six real subsystem products.

Evidence: build/native_probe/phase2-successor-f2-20261012-sol/cycle3-run/{REQUEST.json,RESULT.json,attempt/receipt.env,attempt/child.log}; source manifest SOURCE_MANIFEST_CYCLE2.json and SOURCE2_GIT_RECEIPT.json in the parent packet. Native exit124/timeout after900.288853s, peak4233168KiB observed-only RSS, final_job_active0. All16971 pinned sources and producer/runtime/tool hashes remain unchanged. Zero cache files/objects and no executable. Compilation failure is not a test PASS.

Coordinator started21:12:51.174522+09:00; worker started21:15:16.929979, so pre-worker startup cost145.755s includes SCV cold inventory/snapshot and other admission. The real15857-entry inventory and SCV snapshot receipt were produced. The worker is the retained binary executing `run src/app/cli/native_build_worker.spl`; it ran roughly754s without object output. The log only reports incomplete bug-database coverage. This is not proof that cold SCV alone took146s or that a specific function regressed.

Frozen hotpath audit found one captured Git HEAD and one ls-files listing; noncompilable files filtered before IO; per-file transient scratch digest reduction; unique-create inventory batch and one final sort. No per-file whole-tree scan or repeated Git invocation was established. Actual worker startup attribution remains a profiling/trace investigation, without replaying this exhausted criterion.

All three actual compiler attempts are now closed. Preserve failed scopes/caches and source authority. No fourth identical build, no source receipt bypass, no fabricated object and no restoration of an RSS kill default. A separately authorized Phase1 bootstrap seed build can produce a successor under explicit bootstrap authority and distinct provenance/cache. Production dispatch should eventually use a qualified cached native worker artifact, with cold-start and warm-start evidence; this is a proposal, not an implemented fix.

Remaining acceptance: genuine compiler executable incorporating committed repairs; exact runtime/provider receipts; real native compiler/interpreter/loader products forLLVM andCranelift; complete runtime enumeration/execution ledgers. Current completion0/6, original cases unrun.

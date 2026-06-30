# Feature: memory_audit_gc_nogc

## Raw Request
use spipe dev skill, check nogc mode does actually nogc, gc and nogc spec has no bug, gc, nogc lib has no bug in memory perspective. is there memory perspective needed spespection tool or lib or framwork? check web might usefull things to apply to simple, can on/off without overhead in compile time/runtime? how much overhead for always on. deep research local and web and make small tasks for pherallel devwlopment, assign simple task to sonnet but review it after done.

## Task Type
code-quality

## Refined Goal
Verify that nogc-mode code paths never reach GC allocation at runtime, audit the gc/nogc enforcement specs and the gc_*/nogc_* stdlib trees for memory-perspective bugs, and produce a researched recommendation (local + web) for a memory-inspection tool/framework for Simple that can be toggled with zero compile-time/runtime overhead when off, with measured/estimated always-on overhead — decomposed into small parallel tasks executed by Sonnet agents and reviewed before acceptance.

## Acceptance Criteria
- AC-1: A verification artifact (spec or report) proves whether nogc mode actually avoids GC allocation — e.g. compiling/running a nogc-tree program shows no gc_alloc/GC-runtime calls in emitted code or runtime trace; any violation is recorded as a concrete bug.
- AC-2: Existing gc/nogc enforcement specs (gc_safety, gc_boundary_enforcement, gc_boundary_check, alloc_checker, alloc_inference, memory_capabilities, leak_check fixtures) all run and pass in interpreter mode; failures are triaged as spec bug vs product bug with a written verdict each.
- AC-3: A memory-perspective audit of gc_*/nogc_* lib trees exists with concrete findings (leaks, double-free, dangling/raw-ptr misuse, alloc-in-noalloc, gc-object-in-nogc) — each finding either fixed in a small commit or recorded as a bug doc.
- AC-4: A research report (local + web) exists under doc/01_research/ answering: what memory-inspection tooling fits Simple (sanitizer-style, leak-check, allocation profiler), how on/off toggling can be zero-overhead-when-off (compile-time elision), and what the estimated always-on overhead is (with cited prior art: ASan ~2x CPU/3x mem, heap profilers ~5-10%, etc.).
- AC-5: The work is decomposed into small, disjoint-scope tasks; simple tasks are executed by Sonnet sub-agents in parallel; every Sonnet deliverable is reviewed by the orchestrator (review notes in state log) before being accepted/committed.

## Scope Exclusions
- No Rust seed or C runtime modifications (pure-Simple-first rule); seed findings are recorded as bugs only.
- No full implementation of a new memory-inspection framework — only research, recommendation, and (if trivially small) a pilot hook; the framework build is follow-up work.
- Vendored/third-party sources excluded from audit scope.

## Phase
verify-done

## AC Status
- AC-1 ✅ research_nogc_verify.md — VERDICT: nogc naming-only at runtime (no GC exists; gc=allocate-and-leak; byte-identical binaries); violations recorded in doc/08_tracking/bug/*2026-06-11.md
- AC-2 ✅ research_spec_triage.md — 9 pass / 2 fail / 2 hollow; gc_boundary_check_spec fixed (13/13), alloc_checker_spec de-hollowed (28/28), memory_capabilities 2 failures = product bugs (bug doc filed, left failing deliberately); gc_safety + alloc_inference hollowness recorded in consolidated bug doc
- AC-3 ✅ t5/t6 audit reports; 3 fixes landed (cuda_session leak, noalloc harness alloc, boundary alias detection); remaining findings in gc_nogc_memory_audit_findings_2026-06-11.md
- AC-4 ✅ doc/01_research/runtime/memory_tooling/memory_inspection_tooling.md (+tldr) — 3-tier rec: compile-time @nogc enforcement (0 overhead), MI_DEBUG_FULL+memtrack debug flavor (0 in prod), MI_GUARDED sampling (~0-1% always-on); cited overhead table
- AC-5 ✅ 2 waves × parallel Sonnet agents (disjoint scopes); every deliverable reviewed by orchestrator (diffs read, specs re-run independently, assert_true negative-tested) before path-scoped jj commits

## Log
- dev: Created state file with 5 acceptance criteria (type: code-quality)
- research: 4 parallel agents done. Artifacts: research_nogc_verify.md (VERDICT: nogc naming-only at runtime; no GC exists, gc=allocate-and-leak; lint blind spots; bugs B1 array-push coredump, B3 stub-fallback exit 0), research_local_machinery.md (memtrack/lsan/noalloc_checker infra map), research_web_memory_tooling.md (cited overhead table; top-3: D-style @nogc enforcement, MI_DEBUG_FULL build flavor, MI_GUARDED sampling), research_spec_triage.md (9 pass / 2 fail / 2 hollow).
- implement: launching parallel Sonnet wave T1-T6 (disjoint scopes), orchestrator reviews + commits.
- review(wave1): T1 boundary spec 9/9 re-verified, assertions strengthened — ACCEPT. T7 alloc_checker 28/28 re-verified, no hollow patterns, assert_true negative-tested (fails on false) — ACCEPT. T2 no-cover-up (2 product bugs left failing) — ACCEPT. T3 docs 198+58 lines w/ diagram — ACCEPT. T5/T6 audits — ACCEPT. Committed qzmrrsvu.
- implement(wave2, sec): F1 cuda_session unload-before-overwrite (7/7 contract spec), F2 noalloc harness heap-free (lint OK, no "{ left), F3 GC_ALIAS_MANIFEST alias-evasion detection (13/13). All diffs reviewed + specs re-run by orchestrator. Committed mrmtxwsz (sec).
- verify: 4 bug docs filed (array-push coredump; memory_capabilities crashes; stub-fallback exit 0; consolidated audit findings). AC-1..AC-5 all satisfied.

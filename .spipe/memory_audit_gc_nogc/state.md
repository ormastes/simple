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
implement

## Log
- dev: Created state file with 5 acceptance criteria (type: code-quality)
- research: 4 parallel agents done. Artifacts: research_nogc_verify.md (VERDICT: nogc naming-only at runtime; no GC exists, gc=allocate-and-leak; lint blind spots; bugs B1 array-push coredump, B3 stub-fallback exit 0), research_local_machinery.md (memtrack/lsan/noalloc_checker infra map), research_web_memory_tooling.md (cited overhead table; top-3: D-style @nogc enforcement, MI_DEBUG_FULL build flavor, MI_GUARDED sampling), research_spec_triage.md (9 pass / 2 fail / 2 hollow).
- implement: launching parallel Sonnet wave T1-T6 (disjoint scopes), orchestrator reviews + commits.

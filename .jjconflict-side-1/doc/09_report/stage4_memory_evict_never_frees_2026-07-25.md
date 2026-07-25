# Stage4 memory root cause — 2026-07-25 session

Worktree HEAD: `1ddf2a2b87f` (fetched+reset from origin/main at session start).

## TL;DR

The 111GB Stage4 peak is **not** a new bug — it is the documented
`bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20` retention defect,
already root-caused by three prior sessions down to
`parse_all_impl`/`evict_sources()`/`evict_ast()` in
`src/compiler/80.driver/driver.spl` + `driver_types.spl`. This session added
one new, decisive fact those sessions left untested: **the existing
`--low-memory` eviction functions cannot reduce memory at all, at any
granularity**, because they only drop references (build a fresh container and
reassign) and never call a free/unregister primitive, on a runtime tier that
requires an *explicit* free (no GC, no refcounting). This was proven with a
10-second in-process micro-probe, not inferred.

## Allocation site

- `src/compiler/80.driver/driver_types.spl:166-183` — `evict_sources()`,
  `evict_ast()`, `evict_hir()`. These are the **only** memory-reclamation
  mechanism the driver has, gated by `CompileOptions.low_memory`.
- `src/compiler/80.driver/driver.spl:722-840` (`parse_all_impl`, entry-closure
  branch at 728-787) — retains `entry_sources`/`unique_entry_sources`
  (raw `source.content` for every file in the ~1155-1777-file full-CLI
  closure) and `parsed_entry_modules` (every file's parsed AST) **for the
  whole of phase 2**; eviction only runs once, corpus-wide, at
  `driver.spl:358-360` (`evict_sources`, after phase 2) and `:380-382`
  (`evict_ast`, after phase 3).
- Underlying runtime: `src/compiler_rust/runtime/src/value/heap.rs:172-220`,
  a `HashSet<usize>`-backed `HEAP_ALLOCATION_REGISTRY` with `insert`/`remove`
  called explicitly (`register_heap_ptr`/`unregister_heap_ptr`); its own doc
  comment: *"most no-GC compiler temporaries stay registered for the process
  lifetime"*.

## Mechanism

1. **Corpus-wide retention (previously root-caused, 2026-07-20/24/25
   updates in the linked bug doc):** the full-CLI Stage4 build parses all
   ~1155-1777 files' source text and AST into memory simultaneously before
   any eviction runs. Post string-literal-interning fix (571bb8f8be35,
   confirmed present, `grep rt_string_new_literal` = 4/5 on the binaries used
   this session), retained heap objects are ~2.26/char at ~1.3KB/object
   average. A ~25M-char full corpus times that rate lands in the 70-100GB+
   range — consistent with the fresh 111.0/111.55 GiB measurements already
   taken (not re-run this session, per instructions).
2. **New this session — eviction is a no-op regardless of granularity:**
   `evict_sources()`/`evict_ast()` construct a *replacement* container and
   reassign (`self.sources = metadata`, `self.modules = {}`). On a runtime
   with no GC and no refcounting, dropping the last reference to an object
   does not free it or remove it from `heap_registry` — only an explicit
   `rt_string_free`/`rt_array_free`/`unregister_heap_ptr` call does, and none
   of the three eviction functions makes one. So even a perfect per-file
   rewrite of *where* eviction is called would still show ~0% RSS
   improvement with today's `evict_*` bodies. This reframes the prior
   sessions' stalled "why hasn't a fix landed" question: the blocker was one
   layer earlier than the fingerprint-safety/aliasing questions they were
   investigating.
3. **Fingerprint hazard from the 2026-07-20 doc is now moot:** verified
   `native_sources_fingerprint` is computed once in phase 1
   (`driver.spl:332`, from the un-evicted `self.ctx.sources`) and cached;
   `driver_aot_output.spl:331-334` reads the cached value, not a live
   recompute from (possibly evicted) `source.content`. So per-file source
   eviction is safe w.r.t. the object-cache key — it just wouldn't help
   without also fixing point 2.

## Reduced repro

`evict_probe.spl` (attached, `files/evict_probe.spl`) — no corpus, no
bootstrap, <10s:
```
extern fn rt_heap_registry_count() -> i64
fn main() -> i64:
    val before = rt_heap_registry_count()
    var arr: [text] = []
    var i = 0
    while i < 5000:
        arr = arr.push("dynamic_string_marker_number_padding_padding_padding_" + i.to_text())
        i = i + 1
    val after_fill = rt_heap_registry_count()
    var replacement: [text] = []
    var j = 0
    while j < 5000:
        replacement = replacement.push("")
        j = j + 1
    arr = replacement          # exactly evict_sources()'s pattern
    val after_evict = rt_heap_registry_count()
    print "before={before} after_fill={after_fill} after_evict={after_evict} delta_fill={after_fill - before} delta_evict={after_evict - after_fill}"
    0
```
Build/run (used `build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`,
self-hosted, cranelift, `core-c-bootstrap`, interning-bearing —
`strings -a … | grep -c rt_string_new_literal` = 5):
```
simple native-build --backend cranelift --runtime-bundle core-c-bootstrap \
  --source <isolated-dir> --entry-closure --entry <isolated-dir>/evict_probe.spl -o evict_probe.bin
./evict_probe.bin
```

## Before/after

| step | heap_registry | delta |
|---|---|---|
| start | 0 | — |
| after filling 5,000 dynamic strings | 10,002 | +10,002 |
| after evict-pattern (build fresh container + reassign, dropping the old 5,000 strings + array) | 10,004 | **+2** |

Expected if eviction actually freed: delta_evict ≈ -10,000. Observed: +2
(only the new container's own allocation). **Zero memory reclaimed.**

## Patch

No runtime/driver patch is included. Root-causing why: a real fix needs a
new, application-level deep-free primitive (`text`/`[text]` by value, not a
raw sffi pointer — the only existing `rt_string_free`/`rt_array_free`
callers operate on raw `i64` FFI pointers or are codegen-internal) plus
resolution of the still-open aliasing question from the doc's 2026-07-24
update (whether AST-node `text` fields alias or copy the arena's backing
buffer) before it's safe to free anything beyond `source.content` (which
*is* provably safe to free under `--low-memory`, since its only known
post-phase-2 reader is already gated off in that mode). Building and
validating that primitive is a new, non-trivial runtime change three prior
sessions also declined for the same safety reason — out of this session's
three-cycle budget to do safely. Filed as an addendum to the existing bug
doc (`files/doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`,
"UPDATE 2026-07-25 (this session)" section) with the exact next-step spec:
add the deep-free primitive, validate with `evict_probe.spl`-style
before/after deltas (cheap), only then re-attempt per-file
`evict_sources()` granularity, only then consider one bounded/capped
(`systemd-run -p MemoryMax=...`) full-Stage4 validation run.

## Files

- `files/doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`
  — existing bug doc with this session's addendum appended (repo path:
  `doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`).
- `files/evict_probe.spl` — the reduced repro (repo path is free-standing;
  suggest landing under `test/manual/` or discarding after the primitive
  lands, since it is a diagnostic scratch probe, not product code).

> **Orchestrator verification (2026-07-25).** Independently confirmed:
> `rt_dict_free` = 0 occurrences and `unregister_heap_ptr` = 0 across non-vendor
> `.spl`; `rt_dict_remove` returns the removed value with no free/drop in its body;
> all three CONFIRMED sites exist with zero free calls each.
>
> One correction to the counts below: raw occurrences are `rt_array_free` = 13 and
> `rt_string_free` = 2 (not 0/1). Those include extern declarations, so the number
> of *real call sites* may be lower — but the conclusion is unchanged: eviction and
> clear paths in this codebase essentially never free.
>
> No patches are included, deliberately. The frees could not be proven safe against
> aliasing, and on a no-GC runtime an unproven free is memory corruption — strictly
> worse than the leak it fixes.

# Resource-not-freed audit — other instances of the evict_sources() pattern

Repo: /home/ormastes/dev/pub/simple. No commits/pushes. No bootstrap/stage4 run
(per lane constraint) — findings are grep/code-read plus one interpreter probe.

## Method

1. Enumerated real (non-definition) `.spl` call sites of the free primitives:
   `rt_string_free`, `rt_array_free`, `rt_dict_free` across `src/` (excluding
   vendored runtime).
   - `rt_string_free`: **1** real call site, `src/compiler/70.backend/sffi_minimal.spl:249`.
   - `rt_array_free`: **0** real runtime calls — the 2 hits are LLVM-IR text
     emission (`decls = decls + "declare void @rt_array_free..."`), not actual frees.
   - `rt_dict_free`: **0** call sites anywhere in the non-vendor tree.
   - `unregister_heap_ptr`: only called from inside the Rust registry primitives
     themselves (`heap.rs`, `dict.rs`, `collections.rs`, …) — never from `.spl`.
2. Confirmed by reading `src/compiler_rust/runtime/src/value/dict.rs:349-395`
   (`rt_dict_remove`) that removing a key returns the value to the caller and
   does **not** free/unregister it — the caller owns cleanup, and no `.spl`
   caller does it.
3. Grepped for the "clear by reassignment" idiom (`self.X = {}` / `self.X = []`)
   inside functions named `clear`/`reset`/`evict`/`invalidate`, narrowing 734
   raw hits (mostly harmless constructor init) down to real long-lived
   caches/registries.

## Ranked findings

| # | Site | Allocated per-what | Why nothing frees it | Status | Blast radius |
|---|------|--------------------|-----------------------|--------|---------------|
| 1 | `src/lib/nogc_sync_mut/fs_driver/fat32_cache.spl` — `FatSectorCache`, `ChainCache`, `PathCache`, `ClusterDataCache` (4 classes) | per sector/chain/path/cluster **insert past capacity**, and per `clear()` | `_evict_one()` (lines 49,162,245,337) calls `Dict.delete(k)` on the value dict and the parallel access-time dict, discarding the return; `clear()` (lines 85,183,273,361) reassigns `self.sectors/chains/entries/data = {}`. No free anywhere in the file. | **CONFIRMED** (code read: zero free calls in file; mechanism-confirmed via `rt_dict_remove` source, §2 above) | **High** — `_evict_one()` runs on every cache-full insert, i.e. every sustained FAT32 sector/cluster/chain/path access (SimpleOS board FS driver, disk-image tooling, any FS test that exceeds the small default cache sizes). |
| 2 | `src/lib/skia/feature/glyph_cache/cache.spl` — `GlyphCache` | per unique glyph rasterized beyond cache capacity, and per `clear()` | LRU insert (around line ~60-80) finds the oldest `GlyphCacheEntry` (holding a `GlyphBitmap`, i.e. a pixel buffer) and rebuilds `self.entries` via `rebuilt.append()` skipping the victim index — the victim's bitmap is never freed. `clear()` (line 92) resets `self.entries = []`, dropping every remaining bitmap. | **CONFIRMED** (code read: no free anywhere in file) | **High** — glyph rasterization is a hot path for any sustained text/UI rendering session; cache capacity is small (LRU-by-eviction implies it's meant to be exceeded routinely). |
| 3 | `src/compiler/99.loader/module_resolver/resolution.spl` — `clear_cache()` (line 167) | `resolution_cache` (resolved text paths) and `dir_cache` (`[text]` directory listings from `rt_dir_list`), keyed by cache_key/dir_path | Reassigns `self.resolution_cache = {}` and `self.dir_cache = {}`; old Dict contents (text values, `[text]` arrays) are abandoned, not freed. | **CONFIRMED** (code read) | **Medium** — docstring says "Call between test runs," so it accumulates across a test-runner/daemon session (long-lived process across many test files) rather than per file-resolve; still every `rt_dir_list` result and every resolved path leaks on each clear. |
| 4 | `src/lib/{nogc_sync_mut,nogc_async_mut,gc_async_mut}/cache/{evict.spl,set.spl}` — generic `cache_lru_put/fifo_put/lfu_put/ttl_put` + `cache_*_clear`/`cache_ttl_cleanup` | per eviction (`_remove_at_index` rebuilds `keys`/`values`/`frequencies`/`expiry_times` arrays without the evicted index) and per `cache_*_clear()` (reassigns to `[]`/`{}`) | Same "rebuild array without victim" / "reassign to fresh empty" shape as #1–#3; the evicted `value` (arbitrary heap object) is discarded with no free call anywhere in the 2 files. | **CONFIRMED shape, but SUSPECTED impact** | **Currently ~none**: `grep`/word-boundary search found **zero** callers of `cache_lru_put`/`cache_put`/`cache_lru_clear`/etc. anywhere outside the library's own files, and **zero** `use std.cache` imports anywhere in `src/`. This looks like dead/unwired library code today — but it is the textbook version of the bug, so if/when something adopts it, it inherits the leak immediately. Worth fixing or flagging as unsafe-until-fixed before any caller is added. |

## Probe attempt (fat32 cache) — inconclusive due to unrelated interpreter gap

Wrote `fat32_evict_probe.spl` (using `rt_heap_registry_count()`, same technique
as `doc/09_report/assets/evict_probe_2026-07-25.spl`) to insert 2000 sector
buffers into a `FatSectorCache.new(8)` and diff the registry count. Running it
via `bin/simple run` hit a **separate, pre-existing** interpreter gap:
`Runtime error: Function 'Dict.delete' not found` (repeated once per eviction) —
this matches the already-documented "Interpreter Dict/value quirks" landmine in
memory, not a new bug. Because `.delete()` errors out under the interpreter,
this particular probe could not empirically confirm growth for finding #1 through
that path; the finding stands on the direct code read (no free call exists in
the file, and the mechanism — `rt_dict_remove` returns without freeing — is
independently confirmed by reading `dict.rs`). A native/compiled-mode run (not
attempted here, to respect the "no bootstrap/stage4" constraint) would give a
clean empirical number.

## Not patched

Per the "never land a free you can't prove safe" rule: none of the above were
patched. Fixing #1–#3 requires confirming the evicted values (`[u8]` sector
buffers, `GlyphBitmap`s, cached `[text]`/`text`) are never aliased elsewhere
after being dropped from the cache — that aliasing analysis wasn't done here,
so a free-call fix is left to whoever owns the follow-up (same shape fix as
`evict_sources()`: call `rt_array_free`/`rt_string_free`/`rt_dict_free` — once
those primitives are proven safe for shared-Dict values — before/at the
reassignment or `.delete()` call).

---

## ADDENDUM 2026-07-25 — all three sites re-examined: NONE are safe to patch

Follow-up investigation after `rt_string_free` landed (`d55fe0c67d6`). Outcome:
**no patches applied.** Two independent blockers, plus a correction to this
report.

### The type gate rules out most of it before aliasing even matters

`rt_string_free` → `rt_core_as_string` (`runtime_native.c:1363-1371`) returns
NULL unless `s->kind == RT_VALUE_HEAP_STRING`. The evicted values are:

| site | evicted value type | outcome |
|---|---|---|
| fat32_cache `_evict_one()` | `[u8]`, `[u32]`, `[u8]`, `DirEntry` | refused (not a string) |
| glyph_cache LRU | `GlyphBitmap` (holds `pixels: [u8]`) | refused |
| module_resolver `clear_cache()` | `text` — **only in-scope site** | see below |

There is no proven-safe deep `rt_array_free`, so the array/class sites are not
merely unproven — they are not expressible with today's primitives.

### Aliasing blocks the one in-scope site independently

`resolution.spl:58` stores `resolution_cache[cache_key] = Some(resolved.path)`
and line 59 immediately does `return Ok(resolved)`. `ResolvedModule.path` is a
direct field copy (`types.spl:268-275`) and `RuntimeValue` is `Copy` over a u64,
so the cache entry and `resolved.path` are the SAME pointer, and `resolved`
escapes to the caller. Repeated at 70/87/101/124/137/149. The hit path (39-42)
re-exports the cached string into a new `ResolvedModule` on every hit.

A keys-only variant was considered and rejected: `ModuleResolver` is a `struct`,
so value copies share the Dict pointer; `rt_core_dict_put` keeps the FIRST key
on collision (so a stored key's provenance is not determinable); and it would
reclaim keys while values still leak.

### CORRECTION to this report's own blast-radius claim

The glyph cache at `src/lib/skia/feature/glyph_cache/cache.spl` was described
above as high blast radius. That is **misattributed** — it has NO production
caller; its only reference is `test/01_unit/lib/skia/glyph_cache_spec.spl`
(verified: no non-self references under `src/`). The hot-path glyph cache is a
different class, `src/lib/nogc_sync_mut/text_layout/font_renderer.spl:378`.

Likewise `clear_cache()` has **zero callers** — exported at `__init__.spl:14`,
never invoked (verified: the only textual match elsewhere is a comment in an
unrelated `dns/resolver.spl`). It cannot currently be exercised at all.

### Verification is blocked regardless

`rt_string_free` is not yet callable from `.spl`: the deployed seed predates
`d55fe0c67d6`, so the interpreter raises `unknown extern function:
rt_string_free (E1002)` and returns 0 even for a uniquely-owned value. This is
the standing "extern additions need a bootstrap rebuild" rule.

The native lane is separately broken — see
`doc/08_tracking/bug/native_build_mir_module_has_no_functions_2026-07-25.md`.
Corroborating datum: this investigation's native-build attempts failed with
`unknown extern function: rt_transient_array_scope_begin`, reproduced on the
PRE-EXISTING `assets/evict_probe_2026-07-25.spl`, i.e. not probe-induced. That
is consistent with the isolated finding there that a module-level `extern fn`
is currently mishandled.

**Conclusion: leaving all three leaks in place is the correct action today.** An
unproven free on a no-GC runtime where every assignment aliases is memory
corruption — strictly worse than the leak. Fixing these needs (a) a bootstrap
redeploy so the primitive is callable, (b) the native-build extern defect fixed,
and (c) for the array/class sites, a deep `rt_array_free` that does not exist.

Fixture added: `assets/string_free_semantics_probe_2026-07-25.spl`.

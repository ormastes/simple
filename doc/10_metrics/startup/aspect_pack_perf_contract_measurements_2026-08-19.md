# Aspect-Pack §20 Exact Performance Contract — Measurements, 2026-08-19

Design: `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
§20. Prior static-reading pass: `doc/01_research/compiler/startup_perf/aspect_dynload_startup_loader_perf_research_2026-08-19.md`
(confirms zero §20 numbers existed before this document, and that the segment-
vs-symbol mapping claim (§8.4) is proven only as an arithmetic unit test, not
as a wall-clock number).

Harness: `src/app/test/bench/bench_aspect_pack_perf_contract.spl` (new, this
lane). Run: `bin/simple run src/app/test/bench/bench_aspect_pack_perf_contract.spl`.
Timing is internal (`rt_time_now_unix_micros`), 30 samples per workload,
median + full sample line reported by the harness itself.

**Binary identity for every number below:**
`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
size 59,645,008 bytes, mtime 2026-08-18 10:12:23 UTC (Rust bootstrap seed —
`bin/simple` in this worktree symlinks to it; the seed prints its own
"bootstrap seed only" warning on every run).

**Load at measurement time:** `free -g` showed 66 GB free / 125 GB total
immediately before the run, 63 GB free immediately after (~50 s wall,
finished cleanly, no OOM kill, exit 0). `ps -e | wc -l` ~830-833 processes
throughout. This is lighter than the "earlyoom at 5% free" worst case the task
description warns about, but it is still a shared 32-core box with an unknown
number of concurrent agent sessions — **treat every number below as an upper
bound, not a clean-room figure.** No run in this document hit OOM; none were
discarded.

## Important caveat discovered during this pass: aspect_pack.spl is being rewritten concurrently

`git log -1 --oneline -- src/lib/common/aspect_pack.spl` at measurement time:
`013f1b33a10 feat(loader,aspect): real mmap native layer + segment-granular
mapping, ...`, and the working tree carries a **further uncommitted diff of
+1031/-107 lines** on top of that (another agent's live edit, per this lane's
"five other agents own the loader/aspect_pack sources" constraint). Effect
measured directly: `apk_load_facet(ld, catalog, "debug/Debuggable")`, called
with the exact fixture from the existing passing unit test
(`test/01_unit/lib/aspect_pack_spec.spl` REQ-APK-04 — same 3-module pack,
same payload sizes 40/60/50 repeats, same catalog, same pack_path), returns
`ok=false found=false error_code=APK_MODULE_CORRUPT error_message="frame size
does not match directory"` right now, reproduced independently with a
minimal 15-line debug script outside the harness. This is **not** a bug in
the harness or its payload choice — it reproduces byte-for-byte on the known
passing fixture. It means: **the first-use and cache-hit/miss numbers below
are timings of the FAILURE path, not a successful facet load** — the call
still returns in bounded, exception-free time, so the *shape* of the number
(catalog lookup + pack lookup + attempted decompress, minus the copy/bind
that never completes because it errors first) is still informative as a
lower bound, but it must not be read as "loading a facet costs 170 µs."
Recorded here rather than silently worked around, per this lane's own
instruction not to touch aspect_pack.spl.

## §20 targets stated vs absent

| § | what is stated | is it a measurable target? |
|---|---|---|
| 20.1 cold aspects | qualitative: no pack opened, no payload decompressed, no pages mapped, no per-object state, no path search | **No number stated.** Boolean/counter claims only — measurable as counters == 0, not as a latency budget. |
| 20.2 hot path (facet-only, static-omitted, patchable) | qualitative: "cost appears only when `facet<T>()` is called"; static-omitted must be byte-identical output; patchable path is "extremely cheap" but explicitly "not described as zero code footprint" | **No number stated anywhere** — not even a qualitative ratio. Also **not reachable** through aspect_pack.spl at all (see Unmeasurable section). |
| 20.3 first use | qualitative cost list (catalog lookup + pack open/index map + validation + selected-closure decompression + relocation + binding publication); explicitly excludes unrelated-module decompression | **No number stated** — a list of cost components, no budget. |
| 20.4 steady state | qualitative: direct witness/vtable entry, inline-cache/hash keyed by `(type_id, facet_id, generation)`, preordered advice chains | **No number stated**, and the witness/vtable dispatch half is **not reachable** through aspect_pack.spl (see below). |
| 20.5 configuration | qualitative: SDN parsed at build/deploy time not runtime; profile selection is "one ID lookup"; disabled profiles cause no pack probing; core cache reusable across profiles | **No number stated.** "One ID lookup" is a shape claim, not a latency budget. |

**Conclusion: §20 as written contains zero numeric acceptance targets.**
Every subsection is a set of qualitative/structural claims (what does NOT
happen, or what shape the cost takes). Nothing in this document was invented
to fill that gap — the table below reports measured values with no target
column populated, because there is no target to compare against.

## Measured values (container/catalog half — reachable today)

| workload | § mapped to | median (µs) | n | sample spread (µs) | evidence class | note |
|---|---|---:|---|---|---|---|
| `apk_open_pack_v1` (pack open) | 20.3 "pack open/index map" | **1** | 30 | 0–1 (all samples 0 or 1) | MEASURED, load-caveated | sub-microsecond; timer resolution-limited, not zero-cost |
| `apk_catalog_route_v1` (catalog lookup) | 20.1 catalog-only read / 20.3 "catalog lookup" / 20.5 "one ID lookup" | **31** | 30 | 30–37 | MEASURED, load-caveated | flat, low-variance — consistent with a hash/index lookup, not a scan |
| `apk_load_module_v1` (per-module inflate+copy, on an already-open pack) | 20.3 "selected dependency-closure decompression" | **55** | 30 | 53–61 | MEASURED, load-caveated | one ~2.4 KB synthetic module (400-line payload); this is the closest proxy to "decompression cost" not contaminated by the corrupt-frame bug, because it uses the pack-level path, not the loader/facet path |
| loader counters on a registered-but-untouched pack | 20.1 "no pack opened / no module decompressed" | packs_opened=0, modules_decompressed=0, bytes_decompressed=0, cache_hits=0 | 1 | — | MEASURED (exact, deterministic) | proxy only: proves the loader *primitive* does no eager work at registration; does not prove a full app-startup path reads only the catalog, because no full-startup harness reaching aspect_pack exists to time |
| `apk_load_facet` (first use, via loader) | 20.3 end-to-end first use | 170 (median), first call 176 | 30 | 167–217 | MEASURED but **not representative** — this is the `APK_MODULE_CORRUPT` failure path (see caveat above), not a completed load | do not use as a first-use budget |
| `apk_load_facet` repeated (cache) | 20.4 "repeated acquisition" | 172 (median) | 30 | 168–550 (one 550 µs outlier, rest tight) | MEASURED but **not representative**, same reason — every repeat call also returned `from_cache=false` (never actually cached, because the first call errored before publishing a binding) | do not use as a cache-hit budget; the `from_cache` field never went true in any of the 30 repeats, so §20.4's registry-reuse claim could not even be exercised |

All four "MEASURED, load-caveated" rows above are genuine successful calls
(no errors), reproducible, internally self-timed, and unaffected by the
`APK_MODULE_CORRUPT` issue because they never touch the loader's facet-bind
path.

## What is NOT measurable today, and why

1. **§20.2 hot path cost of `facet<T>()` dispatch, patchpoint/NOP cost, and
   §20.4 witness/vtable invoke cost** — `src/lib/common/aspect_pack.spl` is
   entirely byte-array/metadata based (`ApkFacetLoadV1.payload: [u8]`); it
   stages module bytes and never invokes them. Per this lane's own prior
   research note and the task brief, the interpreter has a known gap: it
   cannot call through a raw `i64` code address. There is no code path in
   this repo today that executes a loaded aspect module's advice, so there is
   nothing to time for "cost only when `facet<T>()` is called" or "direct
   witness/vtable entry." This is a hard ceiling, not a harness gap.
2. **§20.1 full-application cold-startup behavior** ("the runtime reads the
   application Aspect Catalog only" at process startup) — requires a real
   `bin/simple run` of an application with a wired Aspect Catalog and
   `lazy_facet`/`manual`/excluded aspects, observed via strace/syscall count
   the way `startup_perf_check_2026-08-17.md` did for the general startup
   path. No such wired example application exists in this lane; only the
   library-level loader counters (measured above) are reachable.
3. **§20.3 "selected dependency-closure decompression" vs "excludes unrelated
   modules"** — the single-module `apk_load_module_v1` number above measures
   one module's inflate cost, but proving the closure-selection *boundary*
   (that decompressing module A never touches module B's bytes) needs a
   multi-module dependency graph and a byte-touched instrumentation point
   that does not exist in the current API surface (only aggregate
   `bytes_decompressed` is exposed, not per-module attribution across a
   closure). Not measured; flagged rather than approximated.
4. **§20.3/20.4 first-use and cache-hit real costs** — blocked right now by
   the concurrent `aspect_pack.spl` rewrite (`APK_MODULE_CORRUPT`, see
   caveat). Re-run `src/app/test/bench/bench_aspect_pack_perf_contract.spl`
   once that file's `frame size does not match directory` regression is
   resolved; the harness needs no changes to produce real numbers then — it
   already asserts `from_cache` correctness and will start reporting the
   real success path automatically.
5. **§20.5 "SDN parsed at build/deploy, not runtime"** — this is a claim
   about *when* parsing happens in the build pipeline, not a runtime
   latency; no runtime benchmark can validate or refute it. Would need a
   build-log/trace-point check instead, out of scope for a runtime harness.

## How to reproduce

```bash
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"
free -g
nohup bin/simple run src/app/test/bench/bench_aspect_pack_perf_contract.spl \
  > /tmp/bench_out.txt 2>&1 < /dev/null &
# poll with `ps -p <pid>`, never `timeout`; discard and rerun on exit 137/143 (OOM)
```

# Bounded Rust-seed interpreter caches (memory lifecycle)

- Date: 2026-09-12
- Scope: `src/compiler_rust/compiler/src/**` process-global caches on the seed
  interpreter's module-loading path.
- Out of scope by rule: `src/compiler/80.driver/cache/**`,
  `src/compiler/00.common/cache_contract/**`, any `cache_*authority*` path.

## 1. Inventory — every process-global cache on the seed interpreter path

All of these are `thread_local!` `RefCell` maps, so "process-global" means
per-thread-for-the-life-of-the-thread; the seed interpreter runs the loader on
one thread, so in practice they live for the whole process.

Observed entries = after `bin/simple run src/app/mcp/main.spl --help`, read from
`SIMPLE_CACHE_SIZE_REPORT=1` (`module_cache::report_cache_sizes`).

| # | Cache | File | Key | Value | Growth bound (before) | Eviction (before) | Observed entries | Bounded here? |
|---|---|---|---|---|---|---|---|---|
| 1 | `PARSED_SOURCE_CACHE` | `module_cache.rs:94` | canonical `PathBuf` | `SharedSource` = `Arc<String>` source + `Arc<Module>` AST | none | none | **128** | **yes** (4096) |
| 2 | `PROBE_SOURCE_CACHE` | `module_cache.rs:52` | `(PathBuf, u64)` | `Option<Arc<String>>` whole probe source | none | none | **0** (160 on a `test` entry) | **yes** (4096) |
| 3 | `PATH_KEY_CACHE` | `module_cache.rs:225` | `PathBuf` | `PathBuf` | none | none | **240** | **yes** (16384) |
| 4 | `FILTERED_DICT_CACHE` | `module_cache.rs:227` | `usize` (address of the source dict) | `(Arc<HashMap>, Arc<HashMap>)` | none | none | **115** | **yes** (2048) — §3 |
| 5 | `MODULE_EXPORTS_CACHE` | `module_cache.rs:238` | `PathBuf` | module exports `Value` | none | whole-cache `clear_module_cache*` only | **128** | no — §2 |
| 6 | `MODULE_EXPORT_OWNERS` | `module_cache.rs:239` | `usize` (exports dict address) | `Arc<str>` owner id | none | as above | — | no — §2, §3 |
| 7 | `MODULE_CLASSES_CACHE` | `module_cache.rs:241` | `PathBuf` | `HashMap<String, Arc<ClassDef>>` | none | as above | 128 maps / 165 entries | no — §2 |
| 8 | `MODULE_FUNCTIONS_CACHE` | `module_cache.rs:243` | `PathBuf` | `HashMap<String, Arc<FunctionDef>>` | none | as above | 128 maps / **1,971** entries | no — §2 |
| 9 | `MODULE_ENUMS_CACHE` | `module_cache.rs:245` | `PathBuf` | `HashMap<String, Arc<EnumDef>>` | none | as above | 128 maps / 51 entries | no — §2 |
| 10 | `PARTIAL_MODULE_EXPORTS_CACHE` | `module_cache.rs:252` | `PathBuf` | partial exports `Value` | none | as above | 1 | no — §2 |
| 11 | `MODULES_LOADING` | `module_cache.rs:247` | `PathBuf` set | — | bounded by live recursion depth; entries are removed by `unmark_module_loading` | self-releasing | 0 at rest | n/a — already bounded |
| 12 | `MODULE_GLOBALS_BY_OWNER` | `interpreter_state.rs:398` | `Arc<str>` owner | globals map | none | `clear_module_cache` | — | no — §2 |
| 13 | `MODULE_ENV_BY_OWNER` | `interpreter_state.rs:402` | `Arc<str>` owner | `Arc<HashMap<String, Value>>` | none | `clear_module_cache` | 128 owners / **19,038** entries | no — §2 |
| 14 | `FUNCTION_OVERLOADS` | `interpreter_state.rs:459` | `String` fn name | `Vec<Arc<FunctionDef>>` | none | `clear_module_cache` | **1,864** keys / 3,964 entries | no — §2 |
| 15 | `FUNCTION_MODULE_OWNER` | `interpreter_state.rs:472` | `usize` (FunctionDef address) | `Arc<str>` | none | `clear_module_cache` | — | no — §2, §3 |
| 16 | `LOADER_STATS` | `module_cache.rs:229` | `PathBuf` | visit/eval-time counters | none | none | 0 unless `SIMPLE_LOADER_TRACE=1` | no — diagnostic, off by default |

Two rows the lane guide named that turned out not to be caches at all, recorded
so the next reader does not re-search for them:

- **`interpreter_call/core/*env_cache*` does not exist.** There is no file and no
  symbol matching `env_cache`/`ENV_CACHE` anywhere in `src/compiler_rust/`. The
  nearest real thing is row 13, `MODULE_ENV_BY_OWNER`.
- **`module_resolver/var_overlay.rs` has no cache.** It calls
  `read_trace::rts` (`:110`) and `std::fs::read_to_string` (`:22`) on every
  call with no memo at all, which is why L5-E measured one 1,309-byte file
  re-read 49 times on a single `mcp --help`. That is a *read-count* defect, not
  a retention defect: it retains nothing. Adding a memo there would create a
  17th unbounded cache to then bound, so this lane deliberately leaves it alone.

The `LazyLock<Mutex<HashMap<...>>>` statics under `interpreter_extern/**`
(`SATELLITE_LIBRARIES`, `JIT_INSTANCES`, `WORLDS`, `EVENT_LOOPS`, `SQLITE_*`, …)
are **handle registries**, not caches: their entries are resources with an
explicit open/close lifecycle owned by Simple-level code, and dropping one
behind the owner's back closes a live handle. They are out of scope for a
retention bound and are listed here only so the census is complete.

## 2. Why the module-definition caches are NOT bounded

Rows 5-10 and 12-15 are not memos of a pure function. A module's exports
`Value` is the *result of running that module's top level*; dropping it and
refilling it re-executes top-level statements, which in Simple can print, open
files, register singletons and mutate process state. Eviction would therefore
be observable, and "byte-identical after eviction + reload" — the acceptance
property for every bound in this design — is not available for them.

They are bounded instead by the size of the import graph the process actually
reaches, and they already have a coarse release path (`clear_module_cache`,
`clear_module_cache_selective`) used between test files. Making them
individually evictable needs a re-entrancy-safe module-unload contract, which is
a different piece of work.

## 3. The three `usize`-keyed caches, and why only one of them can be bounded

All three are keyed by a **raw address** (`Arc::as_ptr as usize`). Evicting an
entry can free that allocation, a later object can land on the same address, and
a lookup then finds an entry that describes something else. Whether that is a
wrong answer depends on one detail, and the three differ on it:

- **`FILTERED_DICT_CACHE` re-validates and is therefore safe to bound.** Its hit
  path is `get(&key).and_then(|(src, out)| Arc::ptr_eq(src, dict).then(...))` —
  a recycled address fails `ptr_eq`, which is a **miss and a rebuild**, never a
  false hit. It is bounded here. Its pin predicate covers both maps: an entry
  whose source or filtered map is still referenced elsewhere is exactly an entry
  whose eviction would free nothing, since the allocation survives through that
  other reference.
- **`MODULE_EXPORT_OWNERS` (row 6) and `FUNCTION_MODULE_OWNER` (row 15) cannot
  be.** Neither retains the allocation its key names, and neither re-checks
  anything on a hit: `module_exports_owner` returns whatever
  `MODULE_EXPORT_OWNERS[Arc::as_ptr(dict)]` holds. Their keys are unique only
  because a *different* cache (`MODULE_EXPORTS_CACHE`, `MODULE_FUNCTIONS_CACHE`)
  retains the object for the life of the process. Bounding either of those two
  caches — or these side tables — without adding a re-validation step would turn
  an address recycle into a silent wrong owner. Filed as
  `doc/08_tracking/bug/pointer_keyed_caches_cannot_be_bounded_2026-09-12.md`.

An earlier draft of this section claimed `FILTERED_DICT_CACHE` could not be
bounded either. That was wrong — it missed the `ptr_eq` re-check — and is
recorded here rather than quietly deleted, because the distinction between "raw
address key" and "raw address key that re-validates" is the whole argument.

## 4. The bound

`src/compiler_rust/compiler/src/bounded_cache.rs` — `BoundedCache<K, V>`:
an entry-count limit, approximate-LRU victim selection, and a per-cache pin
predicate `fn(&V) -> bool`.

| property | mechanism |
|---|---|
| retention limit | `limit` entries; `0` means unbounded |
| config | `PARSED_SOURCE_CACHE_MAX_DEFAULT` (4096) / `PROBE_SOURCE_CACHE_MAX_DEFAULT` (4096) / `PATH_KEY_CACHE_MAX_DEFAULT` (16384) / `FILTERED_DICT_CACHE_MAX_DEFAULT` (2048) consts, overridden by `SIMPLE_PARSED_SOURCE_CACHE_MAX`, `SIMPLE_PROBE_SOURCE_CACHE_MAX`, `SIMPLE_PATH_KEY_CACHE_MAX`, `SIMPLE_FILTERED_DICT_CACHE_MAX` |
| an unparseable env value | falls back to the default — a typo must not silently remove a bound |
| cannot evict a borrowed entry | every value handed out is a clone whose payload is `Arc`-shared with the cached copy, so `Arc::strong_count > 1` decides "still borrowed". `SharedSource` checks **both** its `Arc`s (source and AST/error text) |
| failed release | when every over-limit candidate is pinned, the cache **stays over its limit**, bumps `pinned_skips` and stops. An entry is never dropped while borrowed, and never left dangling |
| counters | `*_EVICTIONS`, `*_PINNED_SKIPS`, `*_RETAINED_MAX` in `perf_counters.rs`, reported under `SIMPLE_PERF_COUNTERS=1` |
| cargo-test access | `BoundedCache::set_limit` + `CacheStats`, because env-derived limits latch in a process-global `OnceLock` and cargo runs tests in parallel in one process |
| cost | victim selection is an O(len) scan, and it runs only on an insert that is *over* the limit. On the normal path the defaults exceed the observed high-water, so the scan never runs and the added cost of the bound is one `len()` comparison per fill |

Defaults are chosen **above** the observed high-water of a full
`src/app/mcp/main.spl --help` run, so a default-configured process evicts
nothing and behaves exactly as it did before the bound. The bound is a ceiling
for a process that walks a much larger import graph, not a change to the normal
path.

## 5. Measurements

Binaries: pre-bound `b38e8914` (51,252,904 B) and bounded `b9f787f4`
(51,316,496 B), both built from this worktree with
`cargo build --release --bin simple`, aarch64 Linux, shared host at load ~33.

### The bound, on `src/app/mcp/main.spl --help`

| limit | evictions | pinned_skips | retained_max | stdout |
|---|---:|---:|---:|---|
| default (4096) | 0 | 0 | 128 | 496 B, sha `1330eb61` |
| `SIMPLE_PARSED_SOURCE_CACHE_MAX=8` | 120 | 1 | **9** | 496 B, sha `1330eb61` |

`retained_max = 9` at a limit of 8 is the failed-release property observed live:
one enforcement pass could free nothing because every candidate was borrowed, so
the cache stayed one entry over its limit and counted the skip rather than
dropping a live entry. Stdout is byte-identical across the two, so 120 evictions
and their reloads changed no result.

### Max RSS (`/usr/bin/time -v`, 5 interleaved repetitions per cell, min / mean KB)

| entry | pre-bound `b38e8914` | bounded `b9f787f4` |
|---|---:|---:|
| `run src/app/mcp/main.spl --help` | 336,864 / 337,852 | 337,376 / 338,428 |
| `run` a 3-line file | 37,656 / 38,073 | 37,692 / 37,728 |
| `test .../aspect_catalog_invalidation_spec.spl` | 793,728 / 828,016 | 352,720 / 352,880 |

The first two rows are the expected result: at the default limits nothing is
evicted, so RSS is unchanged (+0.15 % and −0.9 %, both inside the run-to-run
spread).

**The third row is a real, repeatable 55 % drop that this design does NOT claim
credit for.** The counters say the bound evicted nothing on that entry
(`PARSED_SOURCE_EVICTIONS=0`, `PROBE_SOURCE_EVICTIONS=0`, `PATH_KEY_EVICTIONS=0`,
`FILTERED_DICT_EVICTIONS=0`; high-waters 207/160/364/167, all far under their
limits), and re-running the bounded binary with **all four limits set to 0**
— enforcement disabled entirely — still measures 335,532 / 352,648 KB, not
793,728. So eviction is not the mechanism. Both binaries produce an identical
spec verdict (`8 total, 8 passed`), so it is not a short-circuited run either.
The cause is somewhere else in the diff and has not been identified; it is
recorded here as a number, not as a result.

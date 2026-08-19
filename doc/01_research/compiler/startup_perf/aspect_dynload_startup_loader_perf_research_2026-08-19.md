# Aspect Dynload, Startup, Runtime-Compiler and Loader Performance — Research 2026-08-19

Lane: `lane-aspect-dynload`. Method: **static reading only**. No compiler was
run for this document; every number quoted is copied from an existing repo
measurement and attributed to it. The host is memory-critical (see the session
note), so generating fresh measurements was deliberately declined rather than
faked.

## Evidence classes used throughout

| class | meaning |
|---|---|
| **MEASURED** | a number produced by a run recorded in this repo, with the recording cited |
| **CODE-VERIFIED** | a structural claim read directly out of source at a cited file:line |
| **DOCUMENTED-BUT-UNVERIFIED** | a repo document asserts it; I did not re-run or re-derive it |
| **SPECULATION** | inference, explicitly not evidence |
| **not verified** | I looked and could not confirm |

Per `startup_perf_architecture_2026-08-17.md` §12.7, a source contract, a stub,
or an exit-zero run is never performance evidence. That rule is applied here to
this lane's own artifacts, including unflatteringly.

---

## 1. The architecture doc: model, and BUILT vs DESIGNED-ONLY

Source: `doc/01_research/compiler/startup_performance/startup_perf_architecture_2026-08-17.md`
(4,887 lines).

### 1.1 The model in one paragraph

Three orthogonal decisions — *presence* (is a component in the closure),
*placement* (static or dynamic), *activation* (is it turned on) — are resolved
from generated composition data (SCI), not from source imports (§5.1). Stage-0
(`startup()`) does allocation-free argv classification and produces a
`StartupPlanV1` with zero file opens for help/version (§6.4, §6.12). The loader
splits into `loader.base` plus optional capabilities, and maps **one region per
segment rather than one per symbol** (§8.1, §8.4). Execution tiers from a
reference AST/MIR interpreter through a typed ExecIR with quickening and inline
caches to Cranelift (Tier 1) and LLVM (Tier 2), compiling **typed IR, never
source text** (§9.2, §9.14). Aspects are stripped to zero residue when disabled
and dynamically loadable as SMF packs (§7).

### 1.2 §8.4 — one mapping per segment

The doc names the behaviour to retire — a per-exported-symbol loop of
`read → allocate RW → copy → mprotect → icache flush → register` — and
replaces it with: validate directory → build `LoadPlanV1` → reserve address
space → map RX/R/RW **once each** → relocate → seal → one icache flush per
changed code range.

**Status: BUILT for the static SMF path, on the compat loader.**
`src/compiler/99.loader/segment_mapper.spl` (342 lines) implements it and
`src/compiler/99.loader/module_loader_compat.spl:274-315` calls it: distinct
`section_index` values are collected from exported symbols, `map_segment` is
called once per distinct section, and `bind_symbol` per symbol is pure offset
arithmetic that allocates nothing (`segment_mapper.spl:155-181`). CODE-VERIFIED.

**Status: NOT BUILT for the per-function JIT path** — see §3.3 below.

### 1.3 §8.14 — generic instantiation / JIT

Policies `closed` / `preinstantiated` / `on_demand`; the base loader must not
create a compiler automatically. **DESIGNED-ONLY.** No
`ModuleLoaderConfigV2` with a `jit_policy` field exists; the compat loader
still constructs a JIT instantiator eagerly (the doc's own §2.5 says so, and
`src/compiler/99.loader/module_loader_compat.spl` still references `self.jit`
on the source-only branch at `:266`). CODE-VERIFIED as absent.

### 1.4 §8.15 — loader performance targets

Seven ratio targets (tiny SMF load ≤1.5x an OS shared-object load; protection
transitions O(segments) not O(symbols); bounded export lookup; no compiler/JIT
objects in base loader heap).

**Status: exactly one of the seven is proven, and only as arithmetic.**
`test/01_unit/compiler/loader/segment_mapping_count_spec.spl` asserts
`mapping_calls == 2` for 2 segments × 3 symbols, that `mapping_calls` stays
flat when symbols grow 10x (6 → 60 symbols, still 2 mappings), and that
`protection_transitions == 2` for two segments (`:53-82`). It also carries a
negative control that must go RED if a per-symbol load is substituted
(`:94-107`). **No ratio target — nothing against an OS `dlopen`, no bytes-read
target, no heap target — has any measurement anywhere in the repo. Not
verified.**

### 1.5 What else has landed

From `git log` (CODE-VERIFIED that commits exist; not verified that they meet
their targets): WP-02s startup contract (`9ef945e4741`), WP-11s allocation-free
classifier (`e6012f1767d`), WP-12s/13s SCI generator + bounded reader
(`cb42cbd1f19`), WP-15s planner (`66b882d0d0f`), WP-19a-s option router
(`60838dd3f4f`), WP-19b-s CLI extension wire (`0382c8c0ede`), WP-14s static
component table (`acd936994ba`), §8.10/§8.11 `LoadPlanV1`/`LoadReceiptV1`
(`2de7b759b59`), §9.17 persistent code cache (`9d41e819c40`), SIF v1
(`5ffd9e20e59`), §7.4 readiness ladder (`139f2bb34cd`).

The pattern is consistent and worth stating plainly: **contracts, records,
generators and readers have landed; the hot paths they were meant to replace
have mostly not been retired.**

---

## 2. Measured startup cost breakdown

### 2.1 What is actually measured

`doc/10_metrics/startup/startup_perf_check_2026-08-17.md` (MEASURED; seed
binary 59,537,240 bytes, mtime 2026-08-17 12:58:51, load 0.71–1.38):

| command | p50 | syscalls |
|---|---|---|
| `bin/simple --version` | **0.05 s** | statx **10,642**, openat 14, mmap 30 |
| `bin/simple run hello.spl` | **0.06 s** | statx 19, openat 14, mmap 35 |

`doc/10_metrics/startup/cross_language_startup_benchmark_2026-08-18.md`
(MEASURED, but load average 23.8 — the report itself says treat as an
envelope): Simple `run hello.spl` p50 31 ms against C 4 ms, Go binary 7 ms,
python3 43 ms, bun 31 ms; raw runs spanned 21–303 ms, and the report notes
cold-cache startup is several-fold worse than the p50. Max RSS 22,272 kB
against Go's 1,792 kB. `native-build` **fails** on the seed, so no compiled
Simple lane exists to compare — the interpreter is the only measurable lane.

**Dominant single startup cost, measured: the 10,642-statx storm on
`--version`** — 10,145 hits on `.simple/logs/crash_N.log` plus 460 stale probe
files, caused by `cleanup_old_logs` in the Rust seed's `driver/src/log.rs`
calling `path.is_file()` before filtering on the name prefix. It is entirely
seed-side and entirely a function of a 10.6k-file log backlog. It did **not**
fire on the `run` path in that trace.

### 2.2 The three anchors in `.claude/rules/commands.md`, checked

**Anchor 1 — "stdlib read as SOURCE every run, ~82 `.spl` opens, 0 `.smf`":
REFUTED as stated, for the traced case.** `startup_perf_check_2026-08-17.md`
records literally `src/lib opens: 0` for `run hello.spl` and concludes "the
documented '82 src/lib opens per run' baseline did not reproduce for an
import-free script — stdlib loading is evidently lazy on this seed build."
Total `openat` was 14. A separate search found no repo document stating 82.
The nearest real figure is "98 modules vs 4" in
`doc/08_tracking/bug/test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md`,
which is a plausible garbled origin (SPECULATION on the origin; the refutation
itself is MEASURED). **The underlying claim — stdlib is source, not `.smf` —
is not contradicted; the count and the "every run" are.** An import-heavy
program was not traced: not verified.

**Anchor 2 — "`bin/simple lint` has ~12s fixed startup": DOCUMENTED-BUT-STALE,
and `commands.md` says so itself.** The rules file explicitly warns that its
lint-cost table predates the **2026-08-18 06:12 seed redeploy** (env-cache +
parser fixes) and **MUST be re-measured before use**. Those rows are therefore
not quoted here as current. The one post-redeploy measurement that exists is
`doc/10_metrics/startup/cross_language_compute_compile_benchmark_2026-08-18.md`:
a 501-line / 125-function generated arithmetic file lints in **76.5 s**
(repeat 75.6 s) on the 06:12 binary (59,673,480 bytes) — against 0.114 s for
`go build` and 0.254 s for `cc -O2 -c` on the equivalent fixture. The 12 s
startup component itself has **not** been re-measured post-redeploy: not
verified.

**Anchor 3 — "`bin/simple test` has a ~310s Session setup": CONFIRMED as a
recorded measurement, REFUTED as a constant.** Origin is
`doc/08_tracking/bug/test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md`
(`Session setup: 309585ms`, P1, open; the daemon path re-runs the runner from
source, 98 modules vs 4, "no warm cache anywhere"). But the same figure appears
across the repo as 5.1 s, 10.4 s, 141 s, 310 s, 596 s and 873 s;
`doc/08_tracking/test/failure_taxonomy_2026-08-18.md:140` describes it as "a
fixed ~140–310 s per-shard startup" measured under heavy load. Treat it as
**load-dependent, order-of-minutes**, not a constant.

### 2.3 What is not measured at all

- Interpreter **throughput** (ops/sec) as a metric: absent. The compute
  benchmark measures whole-program wall time, which conflates startup and
  throughput.
- Any **loader** timing whatsoever. `segment_mapping_count_spec.spl` counts
  syscalls-by-proxy through mapper counters; nothing times a load.
- Any **aspect** load or activation latency. Confirmed absent from
  `doc/10_metrics/` and `doc/09_report/`.
- Any compiled-mode Simple lane (`native-build` fails on the seed).

---

## 3. Loader: quantifying O(symbols) → O(sections)

### 3.1 Syscall arithmetic per path

From `src/compiler/99.loader/smf_mmap_native.spl`, one `map_segment` costs:

| operation | syscall | count |
|---|---|---|
| `native_alloc_exec_memory` (`:124-138`) | `mmap` (PROT_R\|W\|**X**, MAP_PRIVATE\|ANONYMOUS) | **1** |
| `native_write_exec_memory` (`:157-170`) | **none** — but `rt_ptr_write_u8` **once per byte** | **O(bytes)** |
| `native_make_executable` (`:172-175`) | `mprotect(R\|X)` | **1** |
| `native_flush_icache` (`:177-182`) | no-op on x86 | 0 |
| relocation bracket (`begin`/`end_relocation`) | `mprotect` ×2 | 2 (only if relocs exist) |
| `native_free_exec_memory` (`:151-156`) | `munmap` | 1 |

So a module with **S** sections and **N** exported symbols now costs
**S mmap + S mprotect (+2S if relocated) + S munmap**, versus the retired
**N mmap + N mprotect + N munmap**. For the spec's own fixture the ratio is
2 mappings for 60 symbols — a **30x reduction in mapping calls**
(MEASURED-as-counter, `segment_mapping_count_spec.spl:60-70`; not measured in
time). Real modules typically have 1–2 code sections regardless of symbol
count, so the win scales with N and the mapper's cost does not move at all
(CODE-VERIFIED: nothing in `map_segment` reads symbol count).

### 3.2 Two defects this arithmetic hides

**(a) The byte-copy dominates the syscall saving.**
`native_write_exec_memory` (`smf_mmap_native.spl:157-170`) is a `while` loop
calling the `rt_ptr_write_u8` extern **once per byte**, run in the AST
interpreter. `smf_section_bytes` (`smf_segment_load.spl:53-61`) *also* copies
the section byte-by-byte with `out.push` first. A 64 KiB section is therefore
~131,000 interpreted loop iterations and ~65,500 SFFI crossings before a single
syscall is saved. `rt_memcpy` **does exist** (`src/runtime/runtime_memory.c:608`,
`runtime_native.c:5632`) but takes `uint8_t*`, not the `i64` addresses this
layer uses — so there is no bulk-write extern reachable from here.
CODE-VERIFIED. The header comment at `smf_mmap_native.spl:158-162` documents
why the byte loop was chosen (the `as *u8` cast does not compile) but not that
it costs O(bytes) interpreted work. **This is very likely a net loss against
the per-symbol path it replaced for any module of real size** — SPECULATION on
the sign, because nothing is timed; the O(bytes) cost itself is CODE-VERIFIED.

**(b) The mapping is RWX, which §8.5 forbids.**
`native_alloc_exec_memory:132` uses `PROT_READ | PROT_WRITE | PROT_EXEC`.
§8.5 states "Never create a simultaneously writable and executable segment"
and requires dual-mapping, or RW-then-transition-to-RX. `native_make_executable`
is called afterwards, so the window is short, but the mapping is created RWX.
CODE-VERIFIED; this is a security-policy defect, not only a perf one.

### 3.3 Which path is live for what

| lane | implementation | granularity |
|---|---|---|
| static SMF module load | `module_loader_compat.spl:274-315` → `SegmentMapper` | **per segment** (new) |
| per-function JIT | `jit_instantiator.spl`, `module_loader.spl`, `generation_sweeper.spl` → `object_mapper.map_symbol` | **per symbol** |

The per-symbol JIT path is legitimate under §8.14 (one function compiled at a
time genuinely is one region), so this is not a gap. But note there are **two
different `object_mapper.spl` files**:
- `src/compiler/99.loader/object_mapper.spl:31-58` — `map_symbol` **fabricates**
  an address: `4096 + (generation * 256) + code.len()`. It maps nothing. It is
  a simulation, and the file's own header calls itself a "compatibility surface".
  CODE-VERIFIED.
- `src/compiler/99.loader/loader/object_mapper.spl:70-84` — the real one,
  calling `native_alloc_exec_memory` / `native_make_executable` /
  `native_flush_icache`, in module `compiler.loader.loader.*`.

Both are reachable; `99.loader/__init__.spl:34-38` re-exports the **fake** one
as the package-level `SharedExecMapper`. Which of the two the JIT lane actually
resolves at runtime: **not verified** — it depends on import resolution I did
not trace. This duplication is itself a finding.

### 3.4 The load-bearing hole: mapped code cannot be executed

`native_call_function_0/1/2/3` (`smf_mmap_native.spl:211-243`) **all return 0
unconditionally**, with a comment stating that no mechanism exists to invoke a
raw `i64` code address from this interpreter. The sibling
`loader/smf_mmap_native.spl:246-254` uses `fn_ptr as fn() -> i64` inside
`unsafe:` — the exact form
`doc/08_tracking/bug/loader_interpreter_cannot_call_raw_code_address_2026-08-18.md`
records as failing to **compile** under this seed
(`unsupported cast target type: Pointer`, a whole-file failure, not a skip).
And no `rt_call_ptr_*` extern exists — I grepped `src/runtime/*.c` and found
only `rt_counterpart_invoke` (a different, handle-based ABI). CODE-VERIFIED.

**Consequence, stated as the bug doc states it:** the §8.4 claim is proven as
address arithmetic and as mapping lifecycle, and the native layer beneath it is
now real rather than Dict-simulated (`013f1b33a10`), but **execution of mapped
code is not proven in interpreter mode**. The positive control in
`test/01_unit/compiler/loader/segment_symbol_resolution_spec.spl` is
deliberately left RED (7/8 pass; "expected 33, got 0"). Leaving it red rather
than weakening it is the correct call and should stay that way.

Residual: `_g_fake_memory` still exists at `smf_mmap_native.spl:46` and is
still branched on at `:85-116`, now permanently empty since nothing populates
it — dead simulation scaffolding on the hot path.

---

## 4. Aspect dynload

Source: `src/lib/common/aspect_pack.spl` (894 lines),
`doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
(2,058 lines), coverage matrix at
`doc/09_report/aspect_pack_design_coverage_2026-08-18.md`.

**What is real (CODE-VERIFIED):** container magic and flags (`:62-82`), byte
codecs (`:182-235`), CRC32 framing via `gzip_crc32` (`:236`), real
deflate/inflate through `deflate_compress`/`deflate_decompress` (`:58`), pack
build/open (`:241`, `:351`), module load (`:391`), Aspect Catalog v2 build/open
(`:474`, `:527`), routing (`:553-563`), startup activation (`:780`), ABI
identity check, and loader counters (`:695-707`). Design sections BUILT:
§5.6/5.8/5.9/5.10, §6.7, §9.4, §11.3, §12, §12.3, §13.3, §13.4.

**What is not real, and matters most for performance:**

1. **All I/O is in-memory.** Packs enter via
   `apk_loader_register_pack(ld, path, data: [u8])` (`:710`) — the caller has
   already read the whole file. There is **no mmap, no open, no pread** in the
   module (design §15 is marked MISSING). So the aspect path cannot demand-page
   an aspect; it must fully materialise and fully inflate the container first.
   This is the opposite of the §8.15 "no unselected segment pages" target.
2. **Zero production consumers.** Only the two spec files import
   `std.common.aspect_pack`. No compiler or runtime code does;
   `aop_group_manifest.spl:39` still reads
   `aspect_pack_artifacts: [] # SPEC-FORWARD: no aspect packs yet`. Nothing in
   `src/compiler` *emits* a pack or a catalog.
3. **Not integrated with SMF.** `SectionType::AspectPackDirectory`,
   `AspectPackIndexCache`, `ProfileRecord` have no definitions in `src/`
   (design §23 MISSING).
4. **No measured number exists** for aspect load or activation, anywhere. The
   specs assert loader *counters* (`packs_opened`, `modules_decompressed`,
   `cache_hits`) — counts of work avoided, not latency. Not verified.

So: the aspect dynload container is a genuine, well-tested library, and it is
**not on any live path**, and its performance is **entirely unmeasured**. It
should not be described as a startup cost or a startup win today.

---

## 5. Interpreter and runtime-compiler gaps

### 5.1 It is an AST interpreter with string-keyed environments

- `evaluate_expr` at `src/compiler_rust/compiler/src/interpreter/expr.rs:267`,
  with a discriminant fast-path `route_expr` at `:285` and a fallback big
  `match expr` at `:289`. The comment at `:283-284` records that the previous
  cascade design cost "up to 4 sequential full-enum matches" — a fixed bug, and
  evidence the dispatch shape is where cost lives.
- `Env = CowEnv` at `src/compiler_rust/compiler/src/value.rs:876`; `CowEnv`
  (`:302-328`) holds 5 `HashMap<String,…>`, 4 `HashSet<String>`, and
  `base: Option<Arc<HashMap<String,Value>>>`. Comment `:296-300` explains it
  replaced a plain `HashMap<String,Value>` to avoid deep clones. **Every local
  read is a string hash** across overlay → tombstones → base. There are no
  slot-indexed locals and no `Vec` frame.
- Global tables (`interpreter/core_types.rs:70-112`) are all
  `HashMap<String, …>`, some keyed `(String, String)`.
- Per-expression fixed overhead: a watchdog atomic load (`expr.rs:276`) and the
  profiler hook (`expr.rs:282`).

All CODE-VERIFIED. This matches the doc's §2.6 diagnosis, and §9.2/§9.3's
answer (typed ExecIR with register lanes) is **DESIGNED-ONLY** — no ExecIR
exists.

### 5.2 The inline cache is instrumentation only

`interpreter/dispatch_profile.rs:24-29` declares `IDENT_READS`, `IC_HITS`,
`IC_MISSES` "for judging inline-cache profitability". Grepping all of
`src/compiler_rust/` finds them **only in their own declaration and in the
report printer at `:102-103`** — nothing ever increments them. There is no
inline cache. CODE-VERIFIED. The profiler itself is correctly built (env-gated
`SIMPLE_INTERP_PROFILE`, single relaxed atomic when off) and is the right
first step; it just has not been used to produce a histogram yet — no such
histogram is recorded in `doc/10_metrics/`.

### 5.3 Tier 2 is state-only, and Tier 1 compiles source text

- `src/compiler/95.interp/execution/tiered_jit_manager.spl:12` declares
  `extern fn rt_jit_compile_source(handle, source: text)` — **source text**,
  directly violating §9.14 ("compile from typed IR, never source text").
- Tier 1 (`:86-100`) only sets `JitTier.Fast` when `is_native(name)`.
- Tier 2 (`:101-104`) sets `JitTier.Optimized` and bumps a counter — **no
  compile call at all**. The architecture doc corroborates at `:4865`:
  "Tier 2 transition is state-only — CONFIRMED".
- `src/compiler/70.backend/jit_typed_ir.spl:22-24` (new, untracked)
  self-declares "NOT WIRED: no Cranelift/`rt_jit_*` consumer reads this yet".

CODE-VERIFIED. So the typed-IR JIT foundation is being laid correctly and is
not yet connected to anything.

### 5.4 Other documented perf gaps

DOCUMENTED-BUT-UNVERIFIED, from `doc/08_tracking/bug/`:
`test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md` (P1 open,
~310 s test setup, runner re-interpreted from source);
`lint_single_file_superlinear_timeout_on_line_count_2026-08-06.md` and
`lint_timeout_hwir_zca_rows_2026-08-17.md` (root cause fixed and deployed
2026-08-18 06:12; residual superlinearity not re-characterised);
`module_loader_negative_cache_stat_storm_2026-08-11.md` (loader stat storm —
directly relevant, and §8.12's negative-resolution cache is the designed fix);
`native_build_interpreted_worker_fixed_2_4gb_floor_2026-08-18.md`;
JIT correctness gaps `jit_test_suite_blind_spot_2026-07-30.md`,
`seed_jit_boxed_int_61bit_drops_high_bits_2026-07-22.md`.

One more measured pathology worth naming:
`cross_language_compute_compile_benchmark_2026-08-18.md` §(b) records 100k
string appends at **259.3 s** under Simple JIT versus 0.054 s for bun —
"clearly quadratic (O(n²) copy-per-append)". That is a data-structure defect,
not a startup one, but it is the largest single measured gap in the repo.

---

## 6. Top bottlenecks, ranked by expected win

Ranking criterion: (measured or structurally certain magnitude) × (breadth of
lanes affected) ÷ (cost and risk). Anything whose magnitude is unknown is
ranked lower and said to be so.

### #1 — O(n²) string append (259.3 s vs 0.054 s)
- **Evidence: MEASURED**, `cross_language_compute_compile_benchmark_2026-08-18.md`
  §(b): 100k appends took 259.3 s under Simple JIT after a first attempt hit a
  300 s timeout; bun 0.054 s, Go 0.022 s. Roughly **4,800x** off bun.
- **Why #1:** it is the only four-orders-of-magnitude gap in the repo with a
  real measurement behind it, and string building is on the compiler's own hot
  path (every diagnostic, every codegen buffer, plausibly the lint cost too —
  SPECULATION on that last link).
- **Cost/risk:** medium. Amortised-growth buffer or rope in the runtime string
  representation; localized, but touches a type the whole runtime uses, and the
  `rt_string_*` API has been mass-deleted once before (`6e2f613d302`), so it is
  guarded ground.

### #2 — `bin/simple test` fixed setup, order-of-minutes per invocation
- **Evidence: MEASURED but load-variable.** `Session setup: 309585ms` in
  `test_invocation_fixed_setup_cost_caps_every_sweep_2026-08-17.md` (P1, open);
  141,185 ms recorded independently in
  `failure_taxonomy_2026-08-18.md:140`; a fresh seed showed 5,103 ms. Root
  cause named in the bug: the runner is re-interpreted from source (98 modules
  vs 4) with "no warm cache anywhere".
- **Why #2:** it is paid on **every** verification action by every agent, so it
  multiplies across the whole project's iteration loop. The §9.17 persistent
  code cache has already landed (`9d41e819c40`) — this is about pointing it at
  the runner.
- **Cost/risk:** medium-low. Cache-correctness risk (a stale runner producing a
  false green) is the real danger and must be fail-closed.

### #3 — Interpreter environment: string-hashed locals, no slots, no inline cache
- **Evidence: CODE-VERIFIED** (`value.rs:302-328`, `:876`;
  `core_types.rs:70-112`) plus **MEASURED** whole-program proxies
  (interpreter 1.151 s vs JIT 0.295 s vs Go 0.102 s on the 10⁸-add loop,
  `cross_language_compute_compile_benchmark_2026-08-18.md`). The magnitude
  attributable specifically to env lookup is **not verified** — nobody has run
  the profiler that was just built.
- **Why #3 and not higher:** the structural case is airtight (§2.6 of the
  architecture doc says removing startup overhead alone will never make this
  competitive), but the size of the win is unmeasured, and the doc's own answer
  (typed ExecIR, §9.2) is a large project. The cheap first move — slot-resolved
  locals plus a real inline cache behind the already-declared `IC_HITS`
  counters — is much smaller than ExecIR and would produce the number needed to
  justify ExecIR.
- **Cost/risk:** low for the profiler run, medium for slot resolution, high for
  ExecIR.

### #4 — `native_write_exec_memory` byte-at-a-time SFFI in the segment loader
- **Evidence: CODE-VERIFIED** (`smf_mmap_native.spl:157-170`; plus the second
  byte-loop copy at `smf_segment_load.spl:53-61`). Magnitude: **not verified**
  — no loader timing exists.
- **Why:** it plausibly cancels or reverses this lane's own headline win. Fix
  is small: add an `rt_ptr_write_bytes(addr: i64, bytes, offset)` extern
  wrapping the existing `rt_memcpy` (`runtime_memory.c:608`).
- **Cost/risk:** low. One C function, one extern, one call-site.

### #5 — `--version` 10,642-statx log-dir storm
- **Evidence: MEASURED**, `startup_perf_check_2026-08-17.md`. Seed-side
  (`driver/src/log.rs` `cleanup_old_logs` stats before name-filtering) and
  proportional to a 10.6k-file backlog; **did not fire on the `run` path** in
  that trace, so it does not currently affect hello-world p50.
- **Cost/risk:** trivial (filter by name before `is_file()`, and prune the
  backlog). Ranked #5 only because it is latent rather than currently on the
  hot path — but it is the cheapest fix on this list by a wide margin.

### Not ranked, because the win is unknown: aspect dynload
It has no consumers and no measurements (§4). It cannot be a bottleneck today.
Ranking it would be inventing a number.

---

## 7. PLAN

Ordered. Each step names what would prove it worked — and in every case the
proof is a number or a discriminating test, never a green exit.

**P0. Run the interpreter profiler that already exists.**
`SIMPLE_INTERP_PROFILE=1` on the 10⁸-add loop and on a lint of a known
fixture, writing to `SIMPLE_INTERP_PROFILE_OUT`. One detached process, stamped
binary identity before and after.
*Proves:* an `Expr`-variant histogram lands in `doc/10_metrics/`, and the top
three variants are named. This converts bottleneck #3 from structural argument
into measurement, and should gate any ExecIR work.
*Blocked by:* nothing. This is the cheapest high-value action available and it
is why it is P0.

**P1. Add `rt_ptr_write_bytes` and use it in `native_write_exec_memory`.**
Wrap the existing `rt_memcpy` (`runtime_memory.c:608`) with an `i64`-address
entry point; replace the byte loop at `smf_mmap_native.spl:157-170`; also
replace the `out.push` loop in `smf_section_bytes`.
*Proves:* `segment_mapping_count_spec.spl` stays green (unchanged counters),
plus a new timing on a synthetic 256 KiB section showing the copy cost drop.
Without that timing this is unproven, because the syscall counts do not move.

**P2. Add `rt_call_ptr_0(addr: i64) -> i64` and un-RED the positive control.**
This is option 1 in
`loader_interpreter_cannot_call_raw_code_address_2026-08-18.md` and it is the
only one of the three that does not depend on fixing the pointer cast or on
having a compiled binary.
*Proves:* `segment_symbol_resolution_spec.spl` goes 8/8 with the positive
control **unweakened** — the mapped code returns 33, not 0. Until this lands,
the §8.4 claim must keep being stated as "arithmetic and lifecycle only".

**P3. Fix the RWX mapping (§8.5).**
`native_alloc_exec_memory:132` should map `PROT_READ|PROT_WRITE`, with
`native_make_executable` performing the only R\|X transition.
*Proves:* a new spec asserting no mapping is ever simultaneously W and X;
`segment_mapping_count_spec.spl` protection-transition counts unchanged. Do
this **after** P2, so the positive control can prove the code still executes
through the stricter path.

**P4. Resolve the duplicate loader tree.**
Two `object_mapper.spl` and two `smf_mmap_native.spl` exist under
`99.loader/` and `99.loader/loader/`; the package `__init__` re-exports the
**fabricating** mapper (`object_mapper.spl:31-58`). Determine which the JIT
lane resolves, then delete or explicitly name the other.
*Proves:* a grep showing one definition per symbol, and the JIT specs still
green. Failing to do this means any future loader measurement may be measuring
the simulation.

**P5. Point the persistent code cache (§9.17, landed) at the test runner.**
Attack the ~310 s / ~141 s setup directly.
*Proves:* a before/after `Session setup:` pair from two runs on the same
binary at comparable load, recorded in `doc/10_metrics/`, **plus** a
fail-closed invalidation test showing an edited runner module is not served
from cache. The second half is mandatory — a fast stale green is worse than a
slow honest one.

**P6. Fix string append growth.**
The largest measured gap (#1). Sequence it after P0 only because P0 is hours
and this is days.
*Proves:* the 100k-append fixture from
`cross_language_compute_compile_benchmark_2026-08-18.md` §(b) re-run, showing
sub-second where it showed 259.3 s, and a scaling check at 10k/100k/1M
demonstrating linearity rather than a single point improving.

**P7. Only then: typed ExecIR (§9.2) and real Tier-1/Tier-2 wiring (§9.14).**
`jit_typed_ir.spl` already exists and self-declares NOT WIRED; the tiered
manager still passes source text
(`tiered_jit_manager.spl:12`) and Tier 2 is state-only (`:101-104`).
*Proves:* Tier 2 produces a compilation artifact, not a counter increment —
i.e. a sabotage test in which corrupting the retained source text does **not**
change Tier-2 output (§13.12's own design).

**Standing rule for all of the above:** every measurement records
`readlink -f bin/simple` plus `stat -c '%s %y'` before and after, and states
the load average. On this host, exit 143/137 is an OOM kill and is not a
result.

---

## 8. Known unknowns

Listed rather than papered over.

- Whether the segment loader is a net win in **time**. No loader timing exists
  in this repo. Not verified.
- Which `object_mapper` / `smf_mmap_native` the JIT lane resolves at runtime.
  Not verified.
- The post-2026-08-18-redeploy lint **startup** component (the ~12 s figure).
  Not verified; the rules file's own table is explicitly stale.
- The `.spl` open count for an **import-heavy** program. Only an import-free
  hello was traced (0 `src/lib` opens). Not verified.
- Any aspect-pack latency. Nothing measured. Not verified.
- Whether the 4 `mmap`-count difference between `--version` (30) and
  `run hello.spl` (35) is attributable to anything the loader does. Not
  verified; likely allocator, but that is SPECULATION.

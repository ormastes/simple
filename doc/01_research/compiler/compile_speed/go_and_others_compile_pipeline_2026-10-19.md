# Compile-speed techniques from other toolchains, mapped to Simple (2026-10-19)

Problem: Phase 3 native-builds ~1300 compiler modules. Parse ~2 min (31 procs), HIR ~8 min
(17 procs, 3 GB/worker), mono ~2 min, then MIR lowering single-process ~11 s/module (~4 h)
retaining ~90 GB. Opt-in `SIMPLE_MIR_SHARDING=1` (`src/compiler/80.driver/driver_build/native_mir_shard.spl`,
coordinator `run_mir_shards` in `src/app/cli/native_build_main.spl`) bounds memory by process exit,
but every worker reloads whole-program HIR and re-runs mono. Target: MIR < 10 min on 80 cores.
Sources are from memory (no web access in this session); claims marked "claimed" are vendor numbers.

| # | Technique | What it is / effect | Simple today | Applicability |
|---|-----------|---------------------|--------------|---------------|
| a | **Go export data / unified IR** (`cmd/compile`, `go/internal/gcimporter`, Go 1.20+ unified IR) | Each package compile writes a compact export section (types, inlinable bodies, generic bodies). A compile reads only its *direct* deps' export data, never their sources; work per package is O(own size + deps' interfaces). This is what makes `go build` embarrassingly parallel per package. | Partial: SIF interface files and `interface_digest_of` (`src/compiler/80.driver/driver_build/action_key.spl`), HIR cache (`driver_hir_cache.spl`), mono archive plumbing (`80.driver/cache/hir_mono_archive_consumer_v1.spl`). No consumer loads *only* deps' summaries: MIR workers load the full HIR set. | **Highest gain.** A MIR worker needs: its claimed modules' HIR, the layout/symbol rows of their transitive deps, and the mono instances it must emit. Today it holds ~all 1300 modules' HIR + mono (why the default worker budget is 16 GB, capping concurrency at ~5 on an 83 GB host). Loading export summaries would cut worker RSS toward the HIR shard's 3 GB → ~25+ concurrent workers → 1300 × 11 s / 25 ≈ 10 min. Needs a serialized "MIR-lowering interface" (struct layouts, enum tags, fn signatures, vtable/trait rows, mono instance list with owner module). Large; semantic. |
| b | **GC-shape stenciling + dictionaries** (Go 1.18 generics) | Instantiate one body per *GC shape* (all pointer types share a shape) and pass a runtime dictionary for type-specific ops. Cuts instantiation count and code size; claimed small runtime cost. | No: `40.mono` fully specializes per type-argument list (`monomorphize/cache.spl` keys by def hash + type args). | Medium. Fewer instances → less mono time and less MIR. But Simple's native ABI/layout rules (value-semantics structs, typed storage registry) make shape-sharing a language/ABI design change, not a build fix. Do after (a); measure instance counts per generic first. |
| c | **Go `-c=N` concurrent backend** | Within one package, SSA + codegen of functions run on N goroutines after type-check; claimed ~30-40% wall on large packages. | No: per-module MIR lowering and codegen are sequential per process. | Low/medium now: no shared-memory threads in the self-hosted compiler path that are safe for the lowering arena/transient scopes. Process sharding (already present) gives the same parallelism at module granularity; per-function threading only matters for a few giant modules (stragglers). |
| d | **Go action-ID build cache** (`cmd/go/internal/cache`) | Action ID = hash(tool ID, flags, source hashes, deps' *output* IDs) computed **before** compiling; hit → skip compile entirely. Export-data-only dep keys make cutoff early (dep body change w/o interface change does not rebuild dependents). | Partial: `action_key.spl` (SIF/SMF/witness), content-keyed native object cache (`native_build_cache_scope_key`, `incremental.spl`). But the object witness includes the module's **own MIR**, so a no-change rebuild still lowers every module (hours) just to compute the key. `simple.sdn dependencies:` not traversed. | **High for rebuilds, zero for cold builds.** Key the object on (source hash, deps' `interface_digest_of`, mono-instance set, options) before lowering; skip lowering on hit. Must stay fail-closed (witness re-check on link). |
| e | **Rust incremental + codegen units** | Query system with red/green dep-graph reuse; crate split into N CGUs codegen'd in parallel by LLVM; ThinLTO to recover cross-CGU inlining. | Object cache ≈ coarse incremental; no CGU split; sharding ≈ CGUs at module granularity. | Already approximated by MIR sharding. Lesson: CGU partitioning balances by *estimated cost*, not count — relevant to shard claim order (big modules first). |
| f | **Zig** | Single-process, per-decl incremental with in-place binary patching; aggressive laziness (only analyze reachable decls). | `--entry-closure` gives file-level reachability only. | Low near-term. Decl-level laziness would shrink mono/MIR (unreached fns of reached modules), but needs whole-pipeline demand-driven analysis. |
| g | **OCaml `.cmi` / `.cmx`** | Compiled interface files; dependents recompile only if the `.cmi` digest changes; `.cmx` adds cross-module inlining info. | SIF + `iface_digest` ≈ `.cmi`. | Same as (a)/(d): the artifact exists; the missing piece is consumers that load it *instead of* deps' HIR. |
| h | **Swift WMO vs batch mode** | WMO = whole module in one frontend (best opt, serial); batch = N frontend jobs each owning a file batch but *parsing all files* for lookup — the same redundancy Simple MIR workers have. Swift mitigates via per-file `.swiftmodule` / `.swiftdeps`. | MIR sharding is "batch mode". | Confirms the diagnosis: batch mode's ceiling is the redundant whole-module front half. Fix is (a). |
| i | **C++20 modules (BMI)** | Interface units compiled once to a BMI; importers load the BMI instead of re-parsing headers; claimed large wins over textual includes, limited by build-graph scanning (P1689). | SIF ≈ BMI. | As (a). |

## Ranked for Simple (expected MIR-phase gain)

1. **(a) Export-summary MIR workers** — 5 → ~25+ concurrent workers by RSS; the only path to < 10 min cold. Large, semantic.
2. **(d) Pre-lowering action key** — warm/no-op rebuild from hours to minutes. Medium, must stay fail-closed.
3. **Shard scheduling** (from e): slot pool instead of waves (applied, below), then cost-ordered claims (largest modules first) to kill stragglers. Small, mechanical.
4. **(b) shape stenciling** — after measuring instance counts. Large, ABI-level.
5. **(c)/(f)** per-function threads, decl-level laziness — later.

## Applied in this lane

`run_ledger_shards` (`src/app/cli/native_build_main.spl`) used **wave barriers**: `parallel` workers
started together and the next wave waited for the slowest. With `SIMPLE_MIR_SHARD_COUNT > parallel`
(the documented way to shrink each worker's MIR share) every wave idled on its straggler. It is now a
**slot pool**: a free slot is refilled at once (200 ms poll per live worker via `process_wait(pid, 200)`,
deadline tracked per worker with `time_now_monotonic_ms`). Reap/seal/replace/fail-fast/block handling
is unchanged; replacements still run in the next generation. When `count == parallel` (the default,
and HIR sharding, which shares the function) scheduling is the same, with two deliberate differences on
BOTH lanes: `timeout_ms` now runs from each worker's own spawn (the old sequential waits let the k-th
worker of a wave run up to k x timeout_ms), and reap/log order is exit order rather than index order.
Known gaps filed separately: `doc/08_tracking/bug/shard_timeout_kill_unreapable_and_windows_orphans_2026-10-19.md`
(timeout kill path) and `doc/08_tracking/bug/shard_pool_refill_latency_sequential_poll_2026-10-19.md`.
Verified only by a stubbed interpreter probe on the Rust seed (10 shards / 3 slots: max 3 live, 10
reaped; injected SEGV → CRASH + one replacement). No native build was run. The timeout path is unexercised.

Not applied, and why: "load the coordinator's mono results" — the coordinator never runs mono (it only
drives HIR then MIR workers), so there is nothing to load yet; a serialized mono/layout summary is item (a).
Skipping phases 3-4 in the final link worker was rejected: `compile_to_native` freezes the storage registry
into the cache-scope identity and may read HIR-derived link inputs, so it is not provably semantics-preserving.

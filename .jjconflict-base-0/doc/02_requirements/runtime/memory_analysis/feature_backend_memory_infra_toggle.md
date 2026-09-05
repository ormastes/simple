# Feature: `--mem-infra=` — optional backend memory infra from one Simple interface (2026-07-29)

## Problem
LLVM offers sanitizer/profiling passes (ASan, MemProf, GWP-ASan hooks) that
Cranelift does not. Today none are reachable from `simple build`, and there is
no way to say "give me the best memory checking THIS backend supports".

## Proposal
One flag on build/run/test: `--mem-infra=<a,b,...>` (env
`SIMPLE_MEM_INFRA`). Requests resolve against a per-backend capability
matrix; unavailable items degrade to the closest runtime-level equivalent
with a one-line notice (or hard-error with `--mem-infra-strict`).

| infra          | interpreter | cranelift | llvm | mechanism |
|----------------|-------------|-----------|------|-----------|
| `attr`         | yes         | yes       | yes  | per-owner attribution (runtime choke point) |
| `guard`        | yes         | yes       | yes  | GWP-ASan-style sampled guard pages in rt_alloc |
| `harden`       | yes         | yes       | yes  | debug allocator: quarantine + poison-on-free + canaries |
| `genarena`     | yes         | yes       | yes  | arena generation checks (L6, today's SIMPLE_AST_GEN_CHECK) |
| `strict`       | yes         | no        | no   | strict interpreter mode (Miri-lite: uninit/UAF/provenance) |
| `asan`         | no          | no        | yes  | -fsanitize=address instrumentation of native stages |
| `memprof`      | no          | no        | yes  | -fmemory-profile; PGHO profile out for later feed-back |
| `gpu`          | yes         | no        | no   | CUDA driver-API device-alloc/free byte counters (interpreter_extern/gpu.rs); piggybacks on the `attr` gate |
| `hwasan`/`mte` | no          | no        | yes (aarch64) | hardware tagging — WATCH |

Notes:
- Rows 1-4 are allocator/runtime-level, hence backend-agnostic — this is the
  key design point: `rt_alloc`/heap-registry is a single choke point, so most
  of GWP-ASan's and Scudo's value ports WITHOUT any codegen work.
- `--mem-infra=auto` = `attr,guard,genarena` everywhere + `asan` under LLVM
  debug test builds.
- Existing envs (SIMPLE_AST_GEN_CHECK, SIMPLE_MEM_SNAPSHOT) become aliases of
  matrix rows; no removal.

## Tier × allocator-model coverage (gc, nogc, index-based)

The matrix above is the BACKEND axis. Every infra row must also state its
coverage on the ALLOCATOR-MODEL axis, because malloc-level tools are blind to
index-based allocation:

| allocator model | examples | what sees it |
|-----------------|----------|--------------|
| malloc-backed heap objects | nogc tiers, runtime rt_alloc | attr, guard, harden, asan, memprof — all apply directly |
| GC-managed objects (gc_async_mut) | gpu/cuda/torch tier | attr + counters must hook the GC's alloc/sweep, report live-after-collect, per-collection reclaimed bytes, and survivor attribution (owner tag must survive moves/compaction) |
| index-based arenas / slotmaps | AST arena, ECS stores, handle tables | ASan/GWP-ASan/heaptrack see ONE big block — useless. Coverage comes from instrumenting the ARENA INTERFACE: slot-alloc/slot-free are first-class events feeding attr counters; `harden` = slot poison-on-free + delayed slot reuse (quarantine by index); `genarena` = generation checks (L6) — the guard-page equivalent for slots |
| static pools (nogc_async_mut_noalloc) | baremetal/qemu tier | pool high-water + exhaustion counters only; no dynamic tooling applies |

Requirement: any stdlib arena/pool/slotmap and the GC expose the same small
instrumentation trait (alloc/free/owner/bytes) so ALL runtime-level rows
(attr/guard-equivalents/harden/genarena) work uniformly across gc, nogc, and
index-based allocation — one report, four allocator models.

## Acceptance
- `simple build --backend=cranelift --mem-infra=asan` → notice + `harden`
  fallback (or error under strict); same command with llvm builds
  ASan-instrumented stage and a poisoned-UAF fixture aborts with a report.
- `--mem-infra=guard` catches a seeded UAF fixture within N=1000 alloc
  samples under both cranelift-native and interpreter.
- Matrix documented in `bin/simple build --help`.

## Status (2026-07-30)
CLI flag wiring and capability-matrix resolver library landed (2026-07-30).
Resolver spec `config_spec.spl` passes 12/12. Blocker: compiler does not
currently build with llvm feature at all (LLVM codegen row blocked until
resolved).

## Status (2026-08-05) — `gpu` row added (M7)
Added the `gpu` capability-matrix row (interpreter-only; piggybacks on the
`attr`/`SIMPLE_MEM_ATTR` gate, not a separate env var — see `config.spl`'s
row comment for why it is still a distinct named row). Verified
behaviourally on real GPU hardware (2 CUDA devices, this box): a real device
allocation is deliberately leaked and the `rt_gpu_mem_live_bytes` counter is
shown to report exactly the leaked size, with a balanced alloc+free pair as
a negative control — `test/01_unit/lib/mem_infra/gpu_device_leak_spec.spl`,
5/5 passing. Native-backend (cranelift/llvm) coverage stays unverified/false
per the same conservative posture as `guard`'s pre-2026-08-05 state; see the
row comment in `config.spl` for the exact measurement.

## Non-goals
MSan (needs whole-world instrumentation — strict interpreter mode covers the
uninit class), fleet eBPF profiling.

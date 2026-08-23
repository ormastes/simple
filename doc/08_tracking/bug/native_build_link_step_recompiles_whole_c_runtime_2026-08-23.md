# `native-build`'s "link" step was recompiling the whole C runtime, every build

- **Filed:** 2026-08-23
- **Lane:** PERF (back end)
- **Status:** FIXED — mechanism pinned by `scripts/check/check-runtime-object-cache.shs`
- **Base:** `origin/main` `be0213e30ea`, clean worktree `/mnt/fast/wt-linkperf-1`

## Symptom

`doc/09_report/mir_codegen_optimization_audit_2026-08-23.md` measured step 6/6
`link` at **56,544 ms — 93% of back-end wall** on a hello-world fixture, and
concluded "MIR optimization is not the cost — linking is." Reproduced here at
**102,564 ms of a 108,003 ms build (95%)**.

The conclusion was right about *where*; the name `link` sent it to the wrong
*what*. The step is not dominated by the linker.

## Root cause — measured, not inferred

`strace -f -tt -e trace=execve` over a full `native-build --entry-closure`:

| program | successful execs |
|---|---|
| `/usr/bin/clang` | **27** |
| `/usr/bin/ld.lld` | 1 |
| `/usr/bin/uname` | 64 |

Timeline: first `clang` at `03:14:50.244`, last at `03:16:33.033` — **102.8 s of
serial C compilation**. `ld.lld` starts at `03:16:34.347` and the whole process
exits at `03:16:40.594`, so **the actual link is under ~6 s including teardown**.

The 27 clangs are `src/compiler/70.backend/backend/runtime_compiler.spl`'s
`compile_runtime_objects`: a 27-entry `sources` list (`runtime`,
`runtime_native`, … `counterpart_abi_runtime`) each compiled
`-c -fPIC -O3 -ffunction-sections -fdata-sections` into

```
{tmp_dir}/simple_rt_{compile_pid}_{target}_<name>.o
```

— a **PID-keyed** prefix, which `cleanup_runtime_objects` then deletes. So the
objects can never be reused: every build, in every process, recompiles the
entire C runtime at `-O3`, serially, and throws the result away. Nothing about
this is a link cost; the prebuilt `build/simple-core/libsimple_runtime.a` is not
consulted on this path either.

## Fix

Pure memoization in `runtime_compiler.spl` — no design change, no capability
change, no change to the linker command line, and no change to what is
compiled:

- `_runtime_object_cache_dir()` computes a content key over the compiler path,
  the flag-affecting options (`opt_level`, `include_dynload`,
  `include_stage4_legacy_compat`, target, object extension) **and the path, size
  and mtime of every `.c`/`.h` under the runtime source tree**, then returns
  `{tmp}/simple-rt-objcache/<key>` (override: `SIMPLE_RT_OBJ_CACHE_DIR`).
  Any change to any input misses and recompiles.
- On a hit the object is `cp`-ed to the existing PID-keyed path and `clang` is
  skipped; on a miss it is compiled exactly as before and then published to the
  cache via staging-name + `mv` so a concurrent build never sees a half-written
  object.
- `SIMPLE_RT_OBJ_CACHE=0` disables it entirely (the neuter knob); Windows/MSVC
  hosts and any shell failure fall back to the old behaviour.
- `cleanup_runtime_objects` and every caller are untouched — the temp objects
  are still deleted, only the cache survives.

## Measurement (same fixture, same binary, same machine)

| | before | after (warm) |
|---|---|---|
| `clang` execs per build | **27** | **1** (a probe, not a rebuild) |
| step 6/6 `link` | **102,564 ms** | **4,682 ms** (**21.9×**) |
| whole back end (steps 1–6) | 108,003 ms | 11,379 ms |
| peak RSS of the build process | 2,377,248 kB | 2,376,992 kB |
| produced binary | — | **byte-identical** (`cmp`) |

A cold build after `rm -rf` of the cache still runs 27 clangs and still produces
a **byte-identical** binary — verified in both directions, so the cache is
proven to be a memo and not a behaviour change.

### Peak RSS against the user's < 3 GB link budget

**2.377 GB peak RSS, inside the 3 GB budget**, and unchanged by this fix (it is
the compiler process's own footprint, not the linker's — `ld.lld` is a child
process and never approached it). Recorded here because the budget was asked
for; it is not a defect today.

## Not fixed here (filed instead)

The optimization pipeline still runs more than once per build (measured 2× —
32 `[mir-opt] pass:start` for a 16-pass pipeline; the audit saw 3× on other
paths). See `doc/09_report/rust-perf-limits.md`.

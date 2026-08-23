# PID/clock-keyed build artifacts are structurally unreusable — neighbour sweep of the C-runtime recompile

- Date: 2026-08-23
- Status: **RATCHETED** (census frozen; no fix applied beyond the one already
  landed in `71347b901b6`)
- Guard: `scripts/check/check-no-pid-keyed-build-artifacts.shs`
- Baseline: `scripts/check/pid_keyed_build_artifact_baseline.txt` (32 entries)
- Parent bug: `doc/08_tracking/bug/native_build_link_step_recompiles_whole_c_runtime_2026-08-23.md`

## Why this record exists

`71347b901b6` fixed one instance of a *class*. `native-build` recompiled the
whole C runtime on every build — 27 `clang -c -O3` execs, 102,564 ms of a
108,003 ms hello-world build — because the objects were written to

```
val object_prefix = "{tmp_dir}/simple_rt_{compile_pid}_{target}_"
```

and then deleted. The point is not that a cache was *disabled*: keying a durable
artifact by the producing process's **pid**, by a **wall-clock timestamp**, or by
a **random token** makes reuse *structurally impossible*, because no later run
can ever name the same path. No cache policy can rescue such a path, and the
cost is invisible until someone profiles.

The sweep below asks: where else in the build path is this true?

## Census (2026-08-23, `origin/main` 095a0236045)

Scan: `src/compiler/70.backend`, `src/compiler/80.driver`,
`src/compiler/10.frontend`, `src/app/cli`, all `*.spl`. 32 offenders, all
frozen in the baseline. Highlights by kind:

| kind | sites | example |
|---|---|---|
| C-runtime objects (**already memoised**, `71347b901b6`) | 1 | `runtime_compiler.spl` `simple_rt_{compile_pid}_{target}_` |
| stage4 link staging dirs + archives | 8 | `llvm_native_link_stage4_archives.spl` `simple_stage4_{provider}_{pid}` |
| SimpleOS link objects under **`build/`**, not tmp | 11 | `simpleos_native_linkers.spl` `build/os/simpleos_x86_64_crt0_{pid}.o` |
| LLVM IR/bitcode/object scratch | 6 | `llvm_backend_tools.spl` `simple_wasm_{pid}_{ts}.o` |
| entry/link scratch dirs | 3 | `mold.spl` `{tmp_base}/simple_link_{pid}` |
| driver queue / stderr spill / jit sidecar | 3 | `native_build_main.spl` `{root}/queue-{getpid()}` |

Two of these are worth calling out beyond the ratchet:

1. **`simpleos_native_linkers.spl` writes 11 pid-keyed `.o`/`.c` files into
   `build/os/`, not into a temp dir.** These are durable-looking outputs in the
   repo's own build tree that can never be reused *and* are never garbage
   collected by pid, so `build/os/` accumulates one full object set per SimpleOS
   link. This is the same defect shape as the fixed one, in a location where the
   litter also persists.
2. **`llvm_backend_tools.spl` keys wasm scratch by pid *and* a timestamp**
   (`simple_wasm_{pid}_{ts}.ll/.o`), which is doubly unreusable.

## What was NOT flagged, deliberately

- `foo.{rt_getpid()}.tmp` staging names (`driver_hir_cache.spl:184`,
  `frontend_parse_cache.spl:133`, `cas_store.spl`, `action_index.spl`,
  `incremental.spl`, `runtime_compiler.spl:499`). These are the
  write-temp-then-rename idiom: the **durable** name is the rename target and is
  content-keyed; the pid exists only so two concurrent writers do not collide.
  Removing it would be a correctness regression, not a fix. The guard filters
  them mechanically, and its selftest pins that filter.
- Diagnostic interpolation (`print "[LLVM-LINK] pid={pid}"`).
- `cache/gc/*.spl` and `lease.spl` stamps, which name a *claim*, not an artifact.

## Decision: ratchet, do not bulk-fix

Converting these to content-keyed paths is not a semantics-preserving edit —
each needs its own key design (which inputs affect the artifact) and its own
concurrency story, exactly as `71347b901b6` needed for the runtime objects. Doing
11 of them blind is how the shard-clamp incident happened. So this record freezes
the population and fails any push that ADDS a new one; the individual conversions
are follow-up work, each with its own measurement.

The guard fails in **both** directions — a baselined line that no longer exists
is a stale baseline and also FAILs — because a baseline that no longer describes
the tree is how a ratchet silently stops ratcheting.

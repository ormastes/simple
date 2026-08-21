# Seed interpreter burns ~12 GB RSS / 3.4x wall on one module — ROOT CAUSE FOUND, FIXED

> **2026-08-21 resolution.** Status: **FIXED and LANDED**. Root cause was NOT
> the env-template cache (correctly refuted below) and not any `src/compiler`
> change: it was the **per-call `Env` clone graph**. Every interpreted call
> materialized the callee frame's environment by cloning the caller's env —
> including, for a module function, the module's entire visible-global map —
> and every one of those clones was then RETAINED for the life of the frame
> (and, via closure captures, beyond it). Cost is O(globals) per call in both
> time and memory, so a module with thousands of imported globals paid the
> whole map per call and the retained clones accumulated into multi-GB RSS.
> Capping the template cache could not help, because the templates were not
> what was being retained; the clones were.
>
> **Fix**: a scope-chain `CowEnv`. The callee frame gets a `GlobalScope` — four
> `Arc` handles to the owner's static module env, its import table, and the
> live per-owner global stores — and resolves globals through that parent
> pointer. Nothing is materialized per call, so there is no template to cache
> and no generation to invalidate. Env setup becomes O(args), and the write
> path copies only the one owner map it touches (`Arc::make_mut`) instead of
> the whole store.
>
> **Measured on the same tree and files** (`/usr/bin/time`, shared box):
>
> | probe | before (seed at 47ee75c7cf5) | after |
> |---|---|---|
> | `lint src/compiler/80.driver/driver_types.spl` | 90.5 s / 1.97 GB | **23.1 s / 0.42 GB** |
> | `lint src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` | 759 s / 12 GB | **159 s / 0.66 GB** |
>
> **Regression pins**: `scripts/check/check-lint-cost-budget.shs` (row
> `src/compiler/80.driver/driver_types.spl` at 60 s — verdict
> `PASS ... driver_types.spl=20s/60s`), and the mechanism test
> `src/compiler_rust/compiler/tests/interpreter_call_env_o_args.rs`
> (`per_call_env_setup_does_not_scale_with_module_global_count`), which asserts
> a RATIO, not a wall time, so it holds on a loaded box.
>
> The three `env_template_cache_tests` in `function_exec.rs` were removed with
> the mechanism they pinned (the template cache no longer exists); the six
> `sffi_return_contract_*` tests are untouched and green.


> **2026-08-21 update, read the Numbers section first.** This was filed against
> the unbounded env-template cache. That hypothesis has since been MEASURED AND
> REFUTED: capping the cache (even to 64 entries) does not change peak RSS.
> The memory defect is real; the cache is not its cause. Sections below the
> fold predate the refutation and are kept for the audit trail.

Date: 2026-08-21
Area: `src/compiler_rust` (Rust bootstrap seed, tree-walk interpreter)
Status: FIXED (landed), gated
Related: `doc/08_tracking/bug/seed_interpreter_env_rebuild_per_call_o_globals_2026-08-21.md`
(this defect is a regression introduced by that fix's cache)

## Symptom

Self-hosted stage1 bootstrap
(`<seed> native-build --source src/app --entry src/app/cli/bootstrap_main.spl`)
was far slower than expected; the reported shape was "parse of
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` (4831 lines)
takes many minutes at 4.5 GB RSS".

## What it is NOT: no `src/compiler` regression today

Bisection was run with the seed held FIXED (`/mnt/data/seedperf/simple.v2`) and
only the `src/compiler` tree varied, in a private detached worktree. Probe:
`lint src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` run from
inside the worktree — verified by `strace -e openat` to read 318 files under
that worktree's `src/compiler`, so it does exercise the tree under test.

| tree | wall | peak RSS | verdict |
|---|---|---|---|
| `c9b405ab0a9` (first commit of the day's cluster) | 203.3s | 893 MB | `Lint passed` |
| `dcc38ca8696` (HEAD) | 220.5s | 863 MB | `Lint passed` |

+8.5% across all 46 `src/compiler` commits of the day — inside noise on a shared
box, and far inside the ±30% band. **No `src/compiler` perf regression landed
today.** No further bisection steps were run, because the endpoints already
answer the question. The target file itself grew by only 17 lines over the same
range, so it is not the input either.

## What it IS: the seed binary

Same tree (HEAD), same file, different seeds:

| seed | wall | peak RSS |
|---|---|---|
| `/mnt/data/seedperf/simple.v2` (Fable perf seed) | 220.5s | 863 MB |
| `/mnt/data/.cargo-target-envcache/release/simple` | **744.9s** | **13596 MB** |
| same env-cache seed, `SIMPLE_INTERP_ENV_CACHE=0` | (under build load) | ~957 MB |

3.4x the wall and **15.8x the memory**, from the seed alone. The existing kill
switch `SIMPLE_INTERP_ENV_CACHE=0` removes the memory growth, which localises it
to the env-template cache and nothing else.

## Mechanism

`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs:159-161`
(pre-fix) — `OWNED_ENV_TEMPLATE_CACHE: HashMap<(Arc<str>, usize), EnvTemplate>`,
inserted at `:340` (pre-fix), never evicted.

The key's second component is `Env::template_key()`
(`src/compiler_rust/compiler/src/value.rs:524-532`), which is
`Arc::as_ptr(base) as usize` — the raw ADDRESS of the captured env's immutable
base. A fresh base is allocated for every call frame that owns one, so the key
space is unbounded even though the number of MODULES is small: interpreting a
large file mints a new key per distinct base, and each entry retains a full
`Env` clone plus its `by_source` reverse index (`HashMap<(Arc<str>, String),
Vec<String>>`). Nothing ever removed an entry, so peak RSS tracks the number of
distinct bases the run ever saw, and the allocator pressure shows up as wall
time on top.

Secondary hazard, recorded but not fixed here: because the cache does not retain
the base `Arc`, the address it keys on can be freed and reused by a later,
unrelated base — an ABA hit that would return a stale template. Not observed;
worth closing separately.

## Fix (ATTEMPTED — refuted, see Numbers)

Bound the map. `OWNED_ENV_TEMPLATE_CACHE_CAP` defaults to 4096 entries; on
overflow the whole map is dropped (O(1), no recency bookkeeping on the hot
path). A module in steady state uses far fewer than 4096 distinct bases, so the
original hot-path win is retained; exceeding the cap means base identities are
churning, which is exactly the case where those entries would never be hit
again. `SIMPLE_INTERP_ENV_CACHE_CAP=0` restores unbounded behaviour and is what
the gate uses to prove the fix is load-bearing.

Not a revert: the env-template cache itself is a real and needed optimisation
(it took interpreted phase 1/2 of a stage build from a hang-like 5.5 ms/call to
0.08 ms/call). Only its unbounded growth is removed.

## Numbers — MEASURED 2026-08-21, and they REFUTE the cap hypothesis

All rows below are ONE binary (`/mnt/data/.cargo-target-envcap/release/simple`,
built from this tree with the bound in place), same fixture
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`, so the only
variable is `SIMPLE_INTERP_ENV_CACHE_CAP`:

| cap | wall | peak RSS |
|---|---|---|
| `0` (unbounded — pre-fix behaviour) | (1500s budget) | 11875060 KB (11.3 GB) |
| default (4096) | (1500s budget) | 11994772 KB (11.4 GB) |
| `64` | 758.8s, rc=0 | 11981708 KB (11.4 GB) |

**The bound does not move peak RSS at all.** A 64-entry cap and an unbounded
cap land within 1% of each other, and within 1% of the original 13596 MB
observation. Shrinking the map by 64x changes nothing, which is only possible
if the map is not what retains the memory.

So the diagnosis recorded in the Mechanism section above — "every entry retains
a full `Env` clone plus its `by_source` index, nothing evicts, therefore the map
is the growth" — is **WRONG, and is left in place above only so the refutation
is legible.** Whatever retains ~12 GB is reachable independently of this cache:
evicting the entry does not drop the `Env`, so some other owner holds it (the
`Arc` graph the cloned `Env` points into is the obvious suspect, since dropping
a `HashMap<String, Value>` clone frees only the map spine, not the shared
`Arc`-held values beneath it).

**Status: root cause OPEN.** The memory defect is real and reproduces; the cap
is not its fix. Next step is to find the actual owner — measure retained heap
by allocation site (a heap profiler, or an instrumented count of live `Env`
clones), rather than guessing at another eviction policy.

## What IS fixed here, and is kept

Two things in this change are independently correct and are retained:

1. **ABA hazard on the cache key.** `template_key` is `Arc::as_ptr(base)`, a raw
   ADDRESS, which the allocator may reuse once that base dies — so a key match
   alone could serve a template built for a completely different env. The entry
   now carries a `Weak` of the base and every hit verifies `Arc::ptr_eq`, with a
   dead base failing `upgrade()` and counting as a miss. This is a latent
   correctness bug, not a perf change, and is worth keeping regardless of the
   memory question. Pinned by cargo tests
   `env_template_cache_tests::dropped_base_is_not_a_hit_even_at_the_same_address`
   and `::empty_env_template_matches_only_the_empty_env`.
2. **The bound itself**, kept as cheap insurance against unbounded key growth
   (and pinned by `env_template_cache_tests::owned_env_template_cache_stays_within_cap`),
   but explicitly NOT claimed as the memory fix — the table above shows it is not.

Unblocked along the way: the seed can lint again at all, because the
`Option<T>` return-contract miss that made every seed refuse every input is
fixed — see
`doc/08_tracking/bug/easy_fix_duplicate_typed_arg_nil_return_2026-08-21.md`.
Sanity numbers on a smaller module,
`src/compiler/80.driver/driver_types.spl`: default 90.5s / 1972432 KB,
`CAP=0` 104.5s / 1974256 KB — same story, the cap is not load-bearing.

## Gate — ADVISORY, currently RED

`scripts/check/check-interp-env-cache-bounded.shs` runs the same binary twice on
the same fixture, `CAP=0` vs default, and FAILs unless bounded peak RSS is >3x
smaller. Its `--selftest` (4 fixtures) passes, so the scanner itself
discriminates. Against the real binary it reports:

```
FAIL - 2 run(s) measured, env-template cache is not bounded: unbounded peak
11875060KB vs bounded 11994772KB on
src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl (need >3x separation)
```

That FAIL is **honest and correct**: it is the artifact that refuted the
hypothesis. It lands ADVISORY (not wired into the pre-push guard chain) and must
stay RED until the real retainer is found and fixed, at which point it should go
green and be promoted. Do not "fix" it by widening the ratio or changing the
fixture.

Each run of this gate costs up to two 1500s passes; budget ~50 minutes.

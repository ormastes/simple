# Bug/Analysis: Task #67 "env.clone per nested call" premise is stale — CowEnv already eliminates it

**ID:** seed_interp_env_clone_premise_stale_2026-07-03
**Severity:** P3 — informational; no regression, no fix needed for the described issue
**Status:** Analyzed, closed as already-fixed; smaller residual candidate identified but not actioned (see below)
**Reported:** 2026-07-03

---

## Task as given

Task #67 asked to fix "Rust seed interpreted-worker performance... headlined by env.clone per
nested call," following the prior O(n²) array-push fix (`7180ab09997`, 8.1s→0.04s). Instructions:
measure baseline with a nested-call/recursion/loop benchmark, find the env-clone site in the
call-eval path, apply the smallest fix (Rc/Arc scope chaining, COW, or frame reuse), verify, commit.

## Finding: no per-call full-environment clone exists in the current call path

`src/compiler_rust/compiler/src/value.rs:268-530` already defines `CowEnv` (`pub type Env = CowEnv`)
with the explicit stated purpose: *"This replaces the old `type Env = HashMap<String, Value>` with a
struct that avoids deep-cloning the entire captured environment on every function/lambda call."*
`CowEnv::clone` only `Arc::clone`s the shared `base` and clones the (small) `overlay`/`tombstones`.

More importantly, the actual hot path for a plain named-function call (e.g. recursive `fib(n-1)`,
or any loop calling a top-level `fn`) is:

```
evaluate_call() [interpreter_call/mod.rs:261]
  -> functions.get(name).cloned()          // Arc<FunctionDef> clone — O(1), refcount bump
  -> core::exec_function(...)
       -> exec_function_inner() [function_exec.rs:497]
            let mut local_env = Env::new();   // FRESH EMPTY ENV — no clone of caller/outer env at all
```

`bind_args`/`bind_args_with_values` (`arg_binding.rs`) build the callee's bindings into a **new**
`HashMap::new()` sized to the function's own parameter count — not the caller's environment size.
There is no site in this path that clones the caller's (or any outer) environment wholesale.

The only place a whole-environment `.clone()` still happens is the **closure/lambda call path**
(`exec_function_with_captured_env`, `exec_lambda`, `interpreter_call/mod.rs:275,292,410`), which
clones `captured_env` — proportional to the number of variables the closure actually captured
(typically small), not the caller's full live scope. This is a materially different, much smaller
concern than "env.clone per nested call" as stated, and it is bounded by CowEnv's already-cheap
`Arc`-shared-base clone (though no call site currently populates `base` via `with_base`, so in
practice a closure's clone is still O(captured-var-count), just not O(caller-scope-size)).

## Empirical verification

Benchmarks run against the read-only Rust seed
(`src/compiler_rust/target/bootstrap/simple`, unmodified) with `SIMPLE_EXECUTION_MODE=interpret`
forced (default `run` silently JITs and bypasses the interpreter entirely — first attempt at ~15ms
for fib(27) was measuring the JIT, not the interpreter; this is itself worth noting for anyone
benchmarking "interpreted-worker" perf):

| Benchmark | Time |
|---|---|
| `fib(27)` recursive, plain functions, interpreted | ~1.9–2.2s (832K calls) |
| `fib(27)` + 11 extra unrelated locals bound in caller's scope before the call | ~2.0–2.1s (no measurable difference) |
| 100k-iteration loop calling a 1-arg top-level fn, interpreted | ~15ms |

If a per-call clone were proportional to the *caller's* environment size, adding 11 unrelated
locals to `main`'s scope before calling `fib(27)` would measurably slow every one of the 832K
nested calls. It did not (2.19s vs 2.10s — within noise). This directly falsifies the "clone
caller env per nested call" hypothesis for the plain-function-call path.

## What actually costs time per call (not actioned — diffuse, not a single hotspot)

Per-call fixed overhead in `exec_function_inner`/`execute_function_body` includes: a fresh
`HashMap::new()` allocation for `bound_args` in `bind_args`, `Arc<FunctionDef>` hashmap lookup by
string key, thread-local save/restore of `CONST_NAMES`/`IMMUTABLE_VARS` (via `mem::take`, cheap),
an atomic recursion-depth increment/decrement, string-keyed `local_env.insert()` per parameter, and
general tree-walking overhead in `evaluate_expr`/`exec_block_fn`. No single one of these dominates;
`perf record` was unavailable in this sandbox (`perf_event_paranoid` blocks it, no root) to get a
flamegraph confirming the exact split. Recommendation: if seed interpreter perf work continues,
profile with `perf` on a machine with profiling permissions, or add coarse `std::time::Instant`
counters around `bind_args` vs `exec_block_fn` vs thread-local save/restore to find which fixed
cost dominates before optimizing further — do not re-attempt an env-clone fix, that surface is
already closed.

## Disposition

No code change made. `src/compiler_rust/target/bootstrap/simple` untouched (read-only per task
constraints). This doc records the analysis so the next perf pass doesn't re-derive the same
(incorrect) premise.

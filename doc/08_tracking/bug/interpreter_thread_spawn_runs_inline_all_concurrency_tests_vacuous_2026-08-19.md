# Interpreter `rt_thread_spawn_isolated` runs the closure INLINE — every concurrency test on that path is vacuous

Date: 2026-08-19. Found by lane aspect-dynload while trying to PROVE a
compare-and-swap primitive, not while testing threads.
Severity: repo-wide testing integrity. This silently validates any concurrency
test anyone writes.

## The defect

`src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs:245-360` does
not spawn a thread. It extracts the closure, calls `evaluate_expr` **inline on
the calling thread**, stores the result, and returns a fake handle id.
`rt_thread_join` then just reads the stored value. There is no
`std::thread::spawn` anywhere on that path. The JIT declines too, citing no
closure-ABI representation for bare fn pointers.

## Proof (behavioural, not by reading the source)

A worker that sleeps 500ms before incrementing had **already incremented before
`spawn` returned**:

```
immediately_after_spawn=1        # 0 would mean a real thread
```

## Why this is worse than a missing feature

A contention spec on this path passes for a correct atomic implementation **and
equally for a deliberately racy load/store control**. The agent that found this
wrote exactly such a racy control specifically so it could falsify the test —
and it could not. That is a textbook fake proof, and it means:

- Every existing concurrency test executed via `bin/simple run` / `bin/simple
  test` proves nothing about concurrency.
- Any future concurrency test will also prove nothing, silently.

Real pthreads exist only on the NATIVE path
(`src/runtime/runtime_thread.c:317,348,384` -> `pthread_create`), so a genuine
proof requires a native binary.

## Second, related defect: AtomicBool.compare_exchange is a self-admitted fake

`src/lib/nogc_sync_mut/atomic.spl:156-163` implements `AtomicBool.compare_exchange`
as swap, compare, then **store back on mismatch**, carrying its own comment
`"# Swap back on mismatch (small race window)"`. There is no
`rt_atomic_bool_compare_exchange` in the C runtime — only new/load/store/swap/free.
Anyone building a single-flight guard on `AtomicBool` gets precisely the
duplicate-load bug such a guard exists to prevent.

## What IS real (so the fix is scoped, not a rewrite)

The i64 CAS is genuine. `src/lib/nogc_async_mut/atomic.spl` is a 13-line shim
but it re-exports a real 212-line implementation at
`src/lib/nogc_sync_mut/atomic.spl` (16 live externs at :31-48), backed by C11
atomics: `src/runtime/runtime.c:1394` is
`atomic_compare_exchange_strong_explicit(..., memory_order_seq_cst,
memory_order_seq_cst)`, with real load/store/swap/fetch_add/sub/and/or/xor at
:1370-1435. Verified executing from Simple:
`load=7, cas_expect_hit=true, cas_expect_miss=false, final=42`.

So an earlier refusal of design §14.6 that cited "atomic.spl is a 13-line shim,
no verified CAS" was **wrong in its detail** — an i64 CAS exists and works — but
**right in its conclusion**, for the two reasons above.

## Recommended fix order

1. Add `rt_atomic_bool_compare_exchange` to the C runtime and delete the fake.
2. Make the interpreter's `rt_thread_spawn_isolated*` either spawn a real thread
   or **FAIL LOUDLY**. Silent inlining is the dangerous part: a loud failure
   would have surfaced this years earlier. This is the highest-value item here.
3. Only then build a single-flight activation future (§14.6), with its proof run
   on a NATIVE binary, not the interpreter.

## Also noted while reading

`aspect_pack.spl` `apk_activation_stack_exit_v1` (:1444-1465) pops the top of the
cycle stack **unconditionally, without verifying it matches `(ld, facet_key)`**.
Correct only while every caller nests in strict LIFO — which its docstring
assumes but nothing enforces.

## Addendum: the escape route is also blocked, and the two paths disagree on ABI

An attempt was made to get a genuine contention proof on the NATIVE path (where
`pthread_create` is real). It failed after ~45 minutes on an unrelated backend
defect:

```
llc-20: multiple definition of local value named 'l11'
```

So today there is **no path on which a concurrency claim can be proven**: the
interpreter runs inline, and the native lane does not build.

Worse, the same extern has **incompatible ABIs on the two paths**: the
interpreter demands a `Value::Lambda`, while native demands a raw function
pointer. The JIT declines the program outright with *"no tag-boxed
representation for a bare function pointer"*. So a program written to satisfy one
path will not run on the other, which is why this was not caught by anyone
switching engines.

## Why §14.6 stays unbuilt even if the primitive were proven

All `aspect_pack.spl` loader state is plain non-atomic module-level `var` arrays
(`_fc_*`, `_pk_*`, `_ld_*`, `_stk_*`, around :1310-1345). A CAS-guarded claim word
over non-atomic array state is decoration, not a gate — and there is no execution
path today on which two callers can reach it concurrently. Building the future
first would produce something that looks thread-safe and is not, which is
strictly worse than the current honest absence.

# Stage 3 stalls in `rt_transient_heap_promote` — one enormous scan, NOT quadratic

> **CORRECTION 2026-09-02 (same day, before any fix was attempted).** This record
> originally claimed the cost was O(n^2) because `rt_transient_heap_promote` was
> "called once per module surface". **That is wrong.** There is exactly ONE call
> site — `driver_source_pipeline_parsing.spl:510` — inside
> `parse_all_streaming_surfaces_in_place_impl`, which by its own name and its two
> callers (`:549`, `:554`, the second a retry) runs ONCE over the whole file set,
> not per module. The Simple side already batches correctly: it collects ~24
> arrays per surface into one `roots` array and makes a single
> `module_surface_promote_roots(roots)` call (`module_surface_registry.spl:15-18`).
>
> The measured facts are unchanged and still stand: zero object progress across
> two separate 90s/100s windows, 45+ minutes of worker CPU, and `sample` showing
> the hot leaf as `Vec::retain` (130 samples vs 19 for promote, 18 for
> module_surfaces_promote). What is corrected is the CAUSE attributed to them.
>
> Best current characterisation: a SINGLE `scope.objects.retain(...)` pass over
> the transient scope accumulated for all 760 modules, plus the `Drop` of every
> element it removes. That is O(n) in a very large n with real deallocation work
> per element — slow, possibly legitimately so, and it should terminate. It is not
> a quadratic blowup and it is not proven to be a defect at all.
>
> **What is still unknown and must not be asserted:** the actual length of
> `scope.objects`, whether the time is dominated by the scan or by element drops,
> and therefore whether this is a bug or simply expensive-but-correct work. Those
> need instrumentation, not another stack sample.

**Status:** FIX IMPLEMENTED; staged verification pending
**Filed:** 2026-09-02
**Severity:** P1 — blocks Stage-3 self-host on aarch64-apple-darwin. The stage does not
error and does not deadlock; it burns CPU for a very long time in one large scan.
(Severity retained: whatever the cause, Stage 3 does not complete here.)

## Symptom

Stage 3 reaches `phase=source_closure done=760/760 remaining=0`, then makes no further
progress. The progress sampler reports `status=alive-no-progress`, `stall_streak` climbing
without bound, `tasks_done=1 tasks_total=6`, `current=complete`. Measured directly:
**6,600 object files, zero new in 90 seconds, zero files touched in 3 minutes**, while a
process sat in state `RN` accumulating 69+ minutes of CPU.

This reads as a hang and has been treated as one. A 2026-09-04 replay added the
missing resource evidence: free disk fell from 11 GiB to 146 MiB in four minutes
while the worker reached roughly 2.6 GiB RSS, then returned to 9.8 GiB free as
soon as that worker stopped. The missing space was swap created under promotion
pressure. Continuing would have produced another signal-9 or disk-full failure.

## Evidence — profiler, two independent samples

`sample <pid>` on the live worker, 2s and 5s, both **100% in one chain**:

```
compiler__hir__hir_lowering__module_surface_registry__module_surfaces_promote
  -> rt_transient_heap_promote
    -> std::thread::local::LocalKey::with
      -> alloc::vec::Vec::retain
        -> alloc::vec::Vec::retain_mut
          -> retain::{{closure}}
```

Frame counts from a 4s sample: `module_surfaces_promote` 212, `rt_transient_heap_promote`
212, `Vec::retain` 212, `retain_mut` 209 — i.e. essentially every sample.

## Root cause

The Rust bootstrap runtime inserted a value into `reachable_heap` before asking
whether it was a heap node:

```rust
if !reachable_heap.insert(current.0) { continue; }
if let Some(children) = transient_heap_children(current) { ... }
```

`transient_heap_children` returned `Some(empty)` for immediates. Consequently
every scalar word discovered while scanning raw aggregates was retained in the
heap-identity hash set even though it had neither heap identity nor children.
The compiler surface graph contains enough such words to create multi-gigabyte
hash/swap pressure before HIR. The C and pure-Simple counterparts classify first
and never add immediate words to their heap-node plans.

## Why it was mis-triaged repeatedly

- The stage emits no error, so it looks like a hang.
- `stage3-native-build.log` stays **0 bytes**, so a `grep -c 'E-MIR-TYPE-ZeroKind'`
  returns 0 — a VACUOUS zero that has twice been misread as "the fatal is fixed". Always
  report the log's byte size next to any count.
- The progress sampler reports `cpu_pct=0.0 tree_processes=0` for the supervising pid
  while the real worker is a separate process burning 100% of a core, so the run looks
  idle from the sampler's view.

## Implemented fix

`transient_heap_children` now returns `None` for non-heap immediates. The walker
therefore never inserts them into `reachable_heap`; real heap leaves still return
`Some(empty)` and retain their identity semantics. The focused Rust runtime test
`immediate_words_never_enter_the_reachable_heap_set` executes nil and scalar
representatives and passed (1 test, 0 failures).

## Reproduction

Run Stage 3 on this tree (`--resume-stage3-from-admitted=build/bootstrap` with a valid
receipt) and sample the worker once `phase=source_closure` reports `760/760`. The stack
above appears immediately and persistently.

## Scope note (honest)

The earlier quadratic explanation is withdrawn: promotion is one large scan, as
the correction at the top states. The scalar-set amplification is proven by code
order and the focused classifier test; the 10+ GiB swap delta is measured. A
fresh Stage 2/3 replay is still required to prove end-to-end memory and completion
after rebuilding the Rust bootstrap runtime.

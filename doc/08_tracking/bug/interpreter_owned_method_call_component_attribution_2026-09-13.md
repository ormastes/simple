# Where the 2,950 ns of an interpreted class-method call actually goes

- Status: OPEN (2026-09-13) — two components fixed, the largest one measured and
  left alone; see "Not fixed" below.
- Lane: PERF-7 (interpreter per-call cost), worktree `/home/yoon/dev/simple-perf-7`,
  base `origin/main` d522cc98da2.
- Binaries: BASE `simple.base` sha256 `6903816380d27188...`; ablation PROBE
  `simple.probe` sha256 `1b6feb76f074e0e8...` (measurement-only gates, never
  committed).
- Method: child USER+SYS CPU time, `/usr/bin/time`, interleaved legs, n =
  2,000,000 iterations per fixture, medians and minima over 3-8 repetitions.
  Wall clock is unusable on this host (PERF-6 measured in-process ratios of 0.85
  and 0.96 for a shape doing strictly more work).

## The corpus and what each shape adds

All figures ns/iteration, CPU time, medians over 3 reps at host load ~30-40.

| fixture | shape | ns/iter |
|---|---|---:|
| `ctl_loop` | `acc = acc + 1` in a `while` | **~0** (taken by PERF-3's inline-int matcher) |
| `f1_free_fn` | `nop()`, free function, empty body | 1,405 |
| `c1_closure` | `acc = acc + f(i)`, lambda | 1,705 |
| `m0_empty_me` | `c.nop()`, class method, body `pass` | 1,865 |
| `m1_bump` | `c.bump()`, body `self.count = self.count + 1` | 2,130 |
| `m2_fn_self` | `acc = acc + c.value()`, non-`me` method | 2,205 |
| `m3_args2` | `c.add2(1, 2)`, two integer arguments | 2,680 |
| `m4_mod_method` | `c.bump()` where the class is in an IMPORTED module | **2,950** |

`m4` is the shape the 21,601 `src/lib/common` call sites actually have: their
classes live in modules, not in the running script. It costs **1.4x** the
script-local `m1` that earlier corpora measured.

## Component table (differences of measured shapes)

| component | ns | how attributed |
|---|---:|---|
| generic statement-walk floor (the loop body itself) | ~1,100 | PERF-6's corpus floor |
| free-function call machinery | ~305 | `f1 − floor` |
| receiver machinery (self bind, resolve, self round trip, write-back pair) | ~460 | `m0 − f1` |
| the method body's one statement | ~265 | `m1 − m0` |
| **module-owner globals path** | **~820** | `m4 − m1` |
| two integer arguments (bind + write-back) | ~550 | `m3 − m1`, i.e. ~275 per argument |

For the representative `m4` shape that is: 37% generic walk, 26% call machinery,
**28% module-owner globals**, 9% body.

## Ablation, and its limit

A probe seed with `SIMPLE_PERF_CALL_ABLATE=<component>` gates (one binary, ten
components, A/B by environment variable so binary identity cannot confound)
splits the owner path further. On `m4`, 8 interleaved repetitions:

| leg | min (ms CPU) | median | delta vs NONE (min / median), ns/iter |
|---|---:|---:|---|
| NONE | 5,050 | 6,050 | — |
| `scope` (`owner_scope()` + `set_scope`) | 4,420 | 5,640 | **315 / 205** |
| `sync` (`sync_owned_captured_globals`) | 4,520 | 5,180 | **265 / 435** |
| `tls` (CONST_NAMES/IMMUTABLE_VARS save+restore) | 4,980 | 5,569 | 35 / 240 |

Every leg produced a byte-identical `sink`, so the deltas are real work removed,
not work skipped.

**The measurement's floor is the finding as much as the numbers are.** In the
first full sweep (3 reps, 3 fixtures, 10 components) several legs came out
*slower* than the unablated control — `shadow` +2,330 ms and `marklocals`
+2,340 ms on `m4`/`m3` — which is impossible for a strict subtraction. Single
repetitions on this host carry ±2,000 ms (±1,000 ns/iter); even at 5
interleaved repetitions nothing below roughly **400 ns/call** separates from the
noise. That is why the two fixes this lane landed are pinned by ALLOCATION
COUNTS and not by a time budget, and why no component below `scope` is claimed.

## The per-call cost grows with the CALLER's frame width

`m5_wide_caller` is `m4` with twenty extra unused `val`s declared in `main`
before the loop. Nothing about the call changes; only the caller frame gets
wider. Measured on the BASE seed, minima over 3 interleaved repetitions:

| fixture | caller locals | min (ms CPU) | ns/iter |
|---|---:|---:|---:|
| `m4_mod_method` | ~5 | 6,360 | 3,180 |
| `m5_wide_caller` | ~25 | 7,659 | 3,830 |

**+650 ns/iteration for 20 extra caller locals — about 33 ns per caller local.**

The mechanism is NOT isolated, and the difference is stated as what it is: a
wider caller frame is wider for everything that walks it, so the loop's own
`i = i + 1` and `while` condition pay part of this too, as may
`capture_node_scope_shadows`. The likeliest call-side contributor is
`publish_and_repoint`: `publish_live_bound_globals` and
`drop_published_globals` each make a full pass over the CALLER's overlay at
three to four hash lookups per entry, and the second additionally collects a
`Vec<String>` of cloned names. Against that, the `publish` ablation on `m4`
measured only ~190 ns single-rep, which does not fit 5 locals at 33 ns each — so
either the per-local term is not all `publish`, or the single-rep ablation is
noise (both are consistent with the noise floor below). Isolating it needs one
control this lane did not have budget to run: `m5` with the method call replaced
by a free-function call, which would separate the call-side term from the
loop-side one.

What survives regardless: **the per-call cost of an interpreted method call
depends on the caller's frame width**, and the corpus's `main` is far narrower
than a real `src/lib/common` function. For real stdlib callers (10-30 locals)
this term is 300-1,000 ns per iteration, and it is invisible to any fixture with
a narrow caller.

The obvious question this raises is whether the publish pass can be restricted to
names the frame actually WROTE. `CowEnv` already tracks `dirty_names` and the
block write-back path is already dirty-only, so the mechanism exists. It is not
attempted here: publishing on call entry is a copy-OUT of the frame's view, and
restricting it changes which of two writers wins when a frame holds a global it
did not write. That needs its own parity spec, not a performance patch.

## Fixed

- The method was resolved TWICE per call (existence pre-check, then the same
  lookup inside the executor) and the class name copied into an owned `String`
  to carry the answer across the `env.remove`. `resolve_object_method` returns
  the resolution itself; six call sites converted; both retired helpers deleted.
- Three throwaway containers per call in argument binding and container
  write-back, none of which a wholly-positional call needs.

Both are counted (`MECALL_METHOD_LOOKUPS`, `MECALL_STRING_ALLOCS`,
`MECALL_CONTAINER_ALLOCS`) and pinned by
`test/05_perf/interp/owned_method_call_parity_spec.spl` plus 15 rows in
`scripts/check/check-perf-regression-tests.shs`.

## Not fixed — the largest component

The **module-owner globals path** (~820 ns, 28% of the representative call) is
`publish_and_repoint` on the caller, `owner_scope()` on the callee, and
`sync_owned_captured_globals` on the way out. `owner_scope` rebuilds the same
`GlobalScope` on every call into the same module: `seed_owner_globals`, a
`MODULE_ENV_BY_OWNER` probe and an `owner_bindings` probe, each a
`HashMap` lookup keyed by the owner's normalised PATH (a ~60-character string
hashed three times per call), plus the snapshot. `publish_and_repoint` makes two
full passes over the CALLER's overlay — `publish_live_bound_globals` and
`drop_published_globals` — at three to four hash lookups per entry, so its cost
grows with the caller frame's width, which in real stdlib code is far wider than
this corpus's `main`.

The obvious fix is to memoise the two rarely-changing per-owner lookups, keyed by
the owner `Arc`'s pointer and invalidated by a generation counter. It is not
landed here because the generation counter has to be bumped at every
`borrow_mut()` of `MODULE_ENV_BY_OWNER` and `MODULE_GLOBAL_BINDINGS_BY_OWNER`
(module_cache restore and clear, module_evaluator insert, `record_owner_binding`,
the interpreter-state clears — eight sites across four files), and it is only
compile-enforced if both `pub(crate)` statics are privatised behind accessors
first. A missed site does not fail loudly: it hands a frame a stale module env,
and the symptom is a wrong global read somewhere else entirely. That is a new
invalidation invariant, not a local change, and landing it unverified in this
lane's remaining budget would have been worse than filing it with its
measurement.

A second, larger idea recorded rather than attempted: a specialised owned-call
kernel for "simple" methods (no defaults, no variadics, no generics, no
contracts, not a generator, not async) that skips `bind_args_with_values_named`
and most of `execute_function_body`'s bookkeeping — the call-path analogue of
what PERF-3 did for while loops. The component table says the ceiling for that
is roughly the 765 ns of call machinery, i.e. about a quarter of the call.

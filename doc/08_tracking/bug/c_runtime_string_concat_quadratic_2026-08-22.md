# C runtime: `rt_string_concat` is a fresh malloc+memcpy per append (quadratic builder loops)

**Date:** 2026-08-22
**Area:** `src/runtime/runtime_native.c:2794-2830` (`rt_string_concat`); pure
tree-walk `src/compiler/10.frontend/core/interpreter/ops.spl:49` (delegates to
host `+`)
**Status:** OPEN (filed from the pure-lane audit of the seed's 2026-08-22
memory fixes; not fixed here because the sound fix changes the `RtCoreString`
ABI)
**Seed counterpart:** `Arc::try_unwrap` in-place append for `s = s + x` /
`s += x` (seed interpreter, 2026-08-22). Seed measured after its fix:
`probe_str.spl` N=20k/80k appends = 0.47 s total, 24 MB RSS — linear.

## What was measured

C harness linked against `build/simple-core/libsimple_runtime.a`
(2026-08-21 12:44), appending one char N times through `rt_string_concat`:

| N | wall |
|---|---|
| 10,000 | 0.003 s |
| 40,000 | 0.033 s |
| 160,000 | 1.046 s |

4x N → ~11x then ~32x time: quadratic, as expected from `malloc(len(a)+len(b)+1)`
plus two `memcpy` on every call with no capacity and no in-place path.

`RtCoreString` is `kind / reserved / len / data` — no refcount, no capacity —
so there is nothing for an `Arc::try_unwrap`-style sole-owner check to read.
The runtime already has a capacity-doubling builder, `RtStringBuilder`
(`runtime_native.c:2571-2640`, `rt_string_builder_push` grows ×2 from 64), but
it is used only by `rt_to_string` formatting (`:2959`, `:3026`) and by
`std.common.string_builder`; the `+` operator never reaches it.

## Why not fixed in this change

A sound in-place append needs either a capacity field in `RtCoreString`
(layout change visible to every codegen'd string access) or a codegen-side
sole-owner signal for the `s = s + x` / `s += x` local pattern (a new rt_*
entry point plus MIR pattern lowering). Both cross the rt_* ABI / layering
boundary this lane was told to keep unchanged. The zero-ABI option — having
MIR lower the builder-loop pattern onto `rt_string_builder_*` — is a lowering
feature, not a bug fix.

## Proposed fix (pick one, measure with the harness above)

1. `rt_string_append_inplace(s, x)`: realloc when `s` has spare capacity,
   tracking capacity in the currently-unused `reserved` slot IF every producer of
   `RtCoreString` is audited to zero it (otherwise garbage reads as capacity).
   Lower `s = s + x` / `s += x` on a local `var` to it.
2. Keep `rt_string_concat` as is; lower `var s = ""; loop { s = s + x }` onto
   `rt_string_builder_new/push/finish`.

## Related (same audit, already correct on the pure lane)

`.keys()` / `.values()` / `.entries()` (`runtime_native.c:8201-8224`) allocate
one fresh array per CALL and `rt_for_iterable` (`:8245`) materialises once per
loop, never per iteration — the same contract the seed has after its fix.
Measured 10k-key dict: 1000/4000/16000 `keys()` calls = 0.26/1.08/4.06 s, flat
~260 µs per call, i.e. O(|dict|) per call and no hidden COW clone term (the C
runtime has no refcount; `rt_dict_set` `:8161` mutates in place). A `keys()`
inside a loop body is the caller's O(n²), which `.claude/rules/code-style.md`
already forbids and `check-cow-alias-hotpath.shs` ratchets.

## 2026-08-22 design stop: no ABI-preserving sole-owner fast path exists

Re-audited for an in-place append that keeps the `rt_*` ABI and the
`RtCoreString` layout (`kind / reserved / len / data[]`) unchanged:

- **No ownership signal of any kind.** Strings are registered immortal
  (`rt_core_register_string` -> `rt_core_register_immortal_ptr`) and never
  refcounted. `val t = s; s = s + "x"` makes `t` and `s` the same pointer, so
  any in-place write to `a` after `rt_string_concat(a, b)` is observable
  through `t`. The `reserved` word carries only `SHARED` (cache-owned) and
  `TRANSIENT` (scope-owned) bits; neither distinguishes "one holder" from
  "many holders in this scope".
- **`malloc_usable_size` / a header word cannot supply ownership.** Slack
  capacity is knowable, but capacity without uniqueness is unusable: `data[]`
  is inline, so a result cannot share `a`'s buffer under its own header.
- **A codegen-side signal is a layering change.** The only sound route is a
  new entry (`rt_string_append_owned(s, x)`) emitted by MIR solely for
  `s = s + x` / `s += x` on a local `var` whose previous value has no live
  alias (needs a last-use/escape check in lowering). That is option 1 in the
  record above, and it crosses the rt_*/MIR boundary this lane must keep.

Decision: NOT patched in the runtime. Filed as a lowering feature (option 1
with an escape check, or option 2 builder-loop lowering). Any runtime-only
"fix" here would be a silent aliasing bug, which is worse than quadratic.

## 2026-08-23 follow-on from the same audit: dict delete path

The runtime perf lane re-read this record, confirmed the design stop above
(no ABI-preserving sole-owner path for `RtCoreString`), and left
`rt_string_concat` untouched. Extending the collection audit to the DELETE
path — which the 2026-08-22 pass did not exercise — found a real,
runtime-only, semantics-preserving cost bug of the same class:
`rt_core_dict_put` resized by doubling ONLY, so tombstones from
`d[k] = v; d.remove(k)` grew the table without bound (34.9 MB for a dict with
zero live entries). Fixed by the same-capacity rehash guard the immortal
registry already had. Record:
`c_runtime_dict_tombstone_churn_unbounded_growth_2026-08-23.md`.

## 2026-08-24 re-verification on `origin/main` a9b936ed0cd (still OPEN)

Independently re-measured by a second lane, against `runtime_native.c`
compiled FRESH from `origin/main` (`clang -O2`), not the shared tree's
prebuilt archive. The metric is **total bytes passed to `malloc`**, counted by
interposition — a mechanism number, immune to machine speed (the box was at
load ~63 during this run, so wall clock would have been meaningless):

| N single-char appends | malloc'd bytes | mallocs | ratio vs previous |
|---|---|---|---|
| 10,000 | 50,175,000 | 10,000 | — |
| 40,000 | 800,700,000 | 40,000 | **15.95x** |
| 160,000 | 12,802,800,000 | 160,000 | **16.00x** |

4x N -> 16x bytes is exactly N^2. One `malloc` per append and no capacity, as
the original analysis said. 12.8 GB copied to build a 160 kB string.
Probe: `concat_probe.c` (scratch, not committed — the harness is 30 lines and
is reproduced by the table's method line above).

**The design stop above is confirmed, and one proposed fix is now stale.**

- Option 1's "track capacity in the currently-unused `reserved` slot" is no
  longer available as written: `reserved` is **no longer unused**. It is now
  the string flags word — `RT_CORE_STRING_FLAG_SHARED` (1) and
  `RT_CORE_STRING_FLAG_TRANSIENT` (2), `runtime_native.c:864-874`. Any capacity
  encoding must coexist with those bits (e.g. a log2-capacity class in the
  upper bits), which is a wider audit than the record implies.
- The ABI concern is now concrete, not theoretical: codegen inlines the string
  layout rather than going through `rt_*` accessors — see the "LLVM len fast
  path" reading `RtCoreString`'s `kind`/`len` at
  `src/compiler_rust/compiler/src/codegen/instr/helpers.rs:64` and the
  `kind == 0x53545231` ("STR1") magic compare at
  `src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs:355`. Moving
  `data` out of line (a `char*` + capacity header) would break those inline
  reads in every already-compiled artifact.
- Option 2 / the compiler-side sole-owner signal has a **recorded failed
  attempt**, which future work should not repeat blind.
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1040-1047`
  handles the `x = x + y` -> `x.merge(y)` Pattern-B rewrite and carries an
  explicit `DELIBERATELY NOT HANDLED HERE: a text receiver` comment: an
  `emit_raw_strcat` + copy-back arm was tried there and **measured producing
  "a" instead of "abc"**, so text was left on its existing path rather than
  swapped for a different wrong answer. So the compiler does NOT currently
  carry a sole-ownership proof for strings that a runtime append could lean on
  — `t = s` is a raw tagged-pointer copy the runtime never observes.

Status unchanged: **OPEN**, and correctly so. No runtime-only patch was made.
An in-place append inside `rt_string_concat` without a compiler-provided
ownership proof is an aliasing bug, which is strictly worse than quadratic.
No regression gate was added, because no fix landed — a gate here would pin
nothing.

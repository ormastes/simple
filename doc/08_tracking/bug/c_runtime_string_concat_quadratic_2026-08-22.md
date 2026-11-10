# C runtime: `rt_string_concat` is a fresh malloc+memcpy per append (quadratic builder loops)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## 2026-11-09 re-verification on `origin/release/1.0.0` 7f5215f074f (still OPEN, no runtime patch)

Third-lane re-measurement, same interposition method as 2026-08-24, against
`runtime_native.c` compiled FRESH from `origin/release/1.0.0` (`gcc -O2`,
aarch64, probe links the real `rt_string_concat`; scratch tool, not committed):

| N single-char appends | wall | malloc'd bytes | mallocs |
|---|---|---|---|
| 50,000 | 0.394 s | 1,250,875,000 | 50,000 |
| 100,000 | 1.469 s | 5,001,750,000 | 100,000 |

2x N → 3.73x wall and exactly 4.00x malloc'd bytes: still quadratic, byte
counts still match `sum(sizeof(RtCoreString)+len+1)` exactly (one fresh
`malloc` + two `memcpy` per call, no capacity). The ownership contract was
also re-verified empirically this run: after `s = s + "b"`, a second holder
`val t = s` still observes the OLD bytes (`t` == "a"), so any in-place append
would be a live aliasing bug, exactly as the 2026-08-22/24 design stops
concluded. The `reserved` word remains fully occupied
(`SHARED|TRANSIENT|SESSION|ASCII` = 1|2|4|8), so the stale option-1 capacity
encoding has even less room than before.

Call-site audit at this commit: `rt_string_concat` has exactly four inbound
sites — `rt_any_add`, `rt_tagged_add`, `rt_push` (`+=` receiver), and the
definition itself. There is **no runtime-internal concat-in-a-loop site**, so
the "switch internal loop sites onto `RtStringBuilder`" fallback fixes nothing
either; the builder stays reachable only from `rt_to_string` formatting and
`std.common.string_builder`.

**Conclusion:** a correct fix remains a compiler/MIR lowering feature (option 1
with a last-use/escape check emitting `rt_string_append_owned`, or option 2
builder-loop lowering), not a runtime bug fix. Per this lane's mandate, no
risky runtime hack was landed. Side observation (unrelated, not fixed here):
`scripts/check/check-runtime-concat-nul.shs` does not actually run at this
commit — its compile step fails at link (`undefined symbol: spl_panic`,
referenced from `rt_core_concat_bytes_v1`; `spl_panic` lives in `runtime.c`,
which the script does not link). The failure IS fail-closed (direct
`sh scripts/check/check-runtime-concat-nul.shs` exits 1, measured 2026-11-09),
so the check is RED rather than silently green — but as wired it tests
nothing until the link line gains `runtime.c` or a stub.


## 2026-11-07 — owner decision: diagnose + builder (part A+B landed, C pending)

- **Builder that already exists (A):** `std.common.string_builder`
  (`src/lib/common/string_builder.spl`): `StringBuilder` (parts array,
  `push`/`push_line`/`to_text`/`build`), free constructors `string_builder()` /
  `string_builder_from(s)`, and `RtStringBuilder` backed by the runtime
  `rt_string_builder_new/push/len/finish/free` externs
  (`src/compiler_rust/runtime/src/value/string_builder.rs`, `src/runtime/runtime.h`).
- **Diagnostic (B):** lint `COLL006` (`src/compiler/35.semantics/lint/collection_patterns.spl`)
  fires on `s = s + x`, `s = x + s` and `s += x` inside a loop when `s` is plain
  text. Severity is `WARN`, escalated to `ERROR` under the robust/critical/verified
  safety profiles (`coll006_severity_for_profile`, same rung as
  `E-MIR-EMPTY-ARRAY-ELEM`); `simple lint` prints `error[COLL006]` then. It never
  fires on a builder/buffer target (explicit non-text type or a builder/buffer
  constructor initializer). Fixed a false negative on the way: statement-level
  `s = s + x` (STMT_ASSIGN stores target/value separately) never matched.
  Specs: `test/01_unit/app/lint_spec.spl` "COLL006 scope and robust escalation".
- **Optimization (C):** implemented in `src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl`
  (it replaces the earlier dead stub). The pass matches the lowered pair `tmp = rt_strcat_tagged(s, x); s = tmp`,
  which is what both `s = s + x` and `s += x` lower to (`lower_compound_combine`). It rewrites that pair to
  `sb = rt_string_builder_new(); push(sb, s)` in the preheader, `push(sb, x)` in the loop and
  `s = rt_string_builder_finish(sb)` at every exit. It applies only when all of these hold:
  `s` is a str-typed local referenced in the loop only by the concat pair; the temp is private;
  there is a dedicated preheader; the exits have only loop predecessors; and no
  return/throw/call-terminator leaves the loop. Unknown instruction kinds count as uses.
  The pass is **opt-in** (`SIMPLE_MIR_STRING_BUILDER_OPT=1`) until native verification.
  Specs: `test/01_unit/compiler/60.mir_opt/string_builder_opt_spec.spl` (MIR shape, 10 cases) and
  `string_builder_append_behavior_spec.spl` (equality with the concat loop, and builder scaling
  at N=10k/40k/160k measured 110.9 ms / 399 ms / 1,798 ms on the seed interpreter, i.e. linear).
  Status: **fix-implemented-verification-pending**. Still to do: a native-lane run with the opt-in flag,
  then default-on.

## 2026-11-10 status — P3 runtime-lane triage (worktree simple-p3-rt-20261110)

**Verdict: SUPERSEDED for the `src/runtime` lane — the runtime side is a
recorded, thrice-confirmed design stop, and the owner fix lives compiler-side.**
The 2026-08-22 / 2026-08-24 / 2026-11-09 design stops (the last including the
empirical aliasing proof that after `s = s + "b"` a second holder `val t = s`
still observes the old bytes) stand: any runtime-only in-place append is a live
aliasing bug, strictly worse than quadratic. Verified present at base
1504212d788b: the owner fix is the opt-in MIR string-builder optimization
(`src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl`, gated on
`SIMPLE_MIR_STRING_BUILDER_OPT=1` pending native verification), landed
2026-11-07 per the entry above. `src/runtime` intentionally unchanged.

Side observation (`scripts/check/check-runtime-concat-nul.shs` "tests
nothing"): **already fixed for the Linux lane** by `cc77b18719a6` (2026-11-09,
sound-verdict-oracle pass — the probe now owns a `spl_panic` stub and the
script is verdict-conforming). On this Windows host the check is RED at the
link step (fail-closed, verdict-conforming, but still tests nothing here).
This session attempted a Windows-lane harness repair and stopped per budget
after 3 of 6 cycles; both files were reverted to origin, byte-identical:

1. `-ldl` is passed unconditionally → `lld: unable to find library -ldl`
   (no libdl on UCRT; also broken on Darwin).
2. With `-ldl` made Linux-only: `lld` then reports 19 undefined symbols —
   on PE/COFF, `lld-link --gc-sections` keeps every defined symbol as a gc
   root, so `runtime_native.c`'s full graph must resolve (the only
   constructor is the `_WIN32`-gated binary-stdio ctor at
   `runtime_native.c:4006`, so this is not constructor-rooted; it is the
   COFF exported-symbol root rule). Missing: `spl_print`/`spl_println`/
   `spl_str_*`/`spl_strdup` family, `spl_f64_to_bits`, `rt_simd_has_*`,
   `rt_getcwd`, `rt_sleep_ms_native`, `rt_text_slice_audit_*`,
   `WinHttpCrackUrl`.
3. Linking the designed core-C bridge set (`runtime_legacy_core.c`,
   `runtime_simd_utf8.c`, `runtime_simd_dispatch.c` + `-lwinhttp`, mirroring
   the capsule composition) reduced failures to a single duplicate
   `spl_panic` (probe stub vs `runtime_legacy_core.c:471`) — but the closure
   then grew again (`WSAPoll`/`accept`/`bind` Winsock family via `-lws2_32`,
   `rt_process_run_*`, `rt_open_fd` from `runtime_process.c`). A complete
   fix needs the capsule-grade provider closure (≈19 sources) plus
   cross-platform verification this host cannot run; landing it unverified
   would risk the Linux lane the previous fix already proved.

Follow-up for the owning lane: either run the capsule-grade closure on
Linux/Darwin CI, or scope the probe's runtime surface (compile
`runtime_native.c` with a `-ffunction-sections` + hidden-symbol COFF link).
Labels: windows-lane-compile attempt; host-limited completion.

## 2026-11-11 status — P3 rt2 lane triage (worktree simple-p3-rt2-20261111)

**Verdict: SUPERSEDED-by-prior-lane** — spot-check corroborates the
2026-11-10 p3-rt addendum: the runtime-side thrice-confirmed design stop
stands (any runtime-only in-place append is a live aliasing bug, strictly
worse than quadratic), and the owner fix lives compiler-side. No deep
triage redone.

Spot-check at this lane's base (790b54f7c4fc):

- `src/compiler/60.mir_opt/mir_opt/string_builder_opt.spl` present, still
  opt-in (`SIMPLE_MIR_STRING_BUILDER_OPT` gate at :351, "until verified on
  native" comment at :30); `COLL006` lint owner
  (`src/compiler/35.semantics/lint/collection_patterns.spl`) and both
  pinning specs (`string_builder_opt_spec.spl`,
  `string_builder_append_behavior_spec.spl`) in tree.
- `src/runtime/runtime_native.c` `rt_string_concat` intentionally untouched
  (runtime owns no fix here, by recorded decision).
- seed-smoke (refreshed seed 0791c2b7f4a7): `bin/simple.exe test
  test/01_unit/compiler/60.mir_opt/string_builder_append_behavior_spec.spl
  --mode=interpreter --no-cache` → 3 total, 3 passed, 0 failed (~10 s) —
  builder/concat behavioral equality and linear scaling hold on the seed.

Carried side observation (from prior addendum, out of scope here):
`scripts/check/check-runtime-concat-nul.shs` is fail-closed RED on this
Windows host (link step: PE/COFF gc-root rule pulls the full
`runtime_native.c` closure); a capsule-grade provider-closure repair or a
scoped-probe harness is left for the owning lane. No change made.

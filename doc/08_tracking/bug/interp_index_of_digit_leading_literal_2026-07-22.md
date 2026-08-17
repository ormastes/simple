# Bug: flat `i64?` optional lane collides with tagged-value scheme (seed JIT) — payload 3 reads as nil

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
Observed: 2026-07-22 (as "index_of digit-leading literal" — that was a red herring, twice)
Severity: P1 — silently wrong values in production tooling paths (JIT `run` on
seed-engine binaries, which includes the currently deployed bin/release binary)

## True root cause (isolated, no strings involved)
The seed JIT's **flat (non-boxed) `i64?` lane** does not apply the runtime's
tagged-value scheme (`(v<<3)|tag`), but its values flow into consumers that
dispatch on tag bits. Nil is `rt_core_nil()` = bit pattern **3**
(src/runtime/runtime_native.c ~2402-2422 — the sentinel was moved 0→3 to fix
`native_i64opt_some0_collapses_to_nil`, which only relocated the collision).

Decisive isolation (`fn make_opt(v: i64) -> i64?: return v`, seed JIT):

```
make_opt(0) → some:0          (ok — 0 coincidentally reads as tagged int 0)
make_opt(1) → some:nil        (payload 1 misread via tag bits)
make_opt(2) → some:0.0        (payload 2 misread as float tag)
make_opt(3) → NIL             (payload 3 == nil sentinel — value LOST)
make_opt(4) → some:<value:0x4> (raw repr fallback)
make_opt(11) ?? -99 → prints "true" (11&7=3 tag misread downstream)
```

`SIMPLE_EXECUTION_MODE=interpreter` is CLEAN (real Rust Value enum, no packing).

## Surface symptoms (how it was found)
`text.index_of(needle)` "returns nil for any match at position 3" — because the
found index 3 IS the payload-3 collision. All string-search implementations
(spl_str_index_of, rt_string_find, SIMD family) verified CORRECT. Earlier
"digit-leading literal" and "position 3 search miss" characterizations were
both artifacts of this. Every `i64?`-returning API (find/rfind/index_of/
last_index_of/dict lookups/...) mis-nils on payload 3 and misprints small
payloads.

## Affected engines / binaries
- Seed JIT (`run` default): AFFECTED — confirmed. Note the wt_e2ebootstrap
  "full" binary delegates run to a sibling `simple_seed`; the deployed
  bin/release/x86_64-unknown-linux-gnu/simple is ALSO seed-engine (banner) and
  reproduces — consistent with the known "self-hosted not deployed" blocker.
- Interpreter: NOT affected — confirmed.
- Seed native/LLVM codegen: untested, likely affected (same dispatch tables,
  codegen/llvm/functions.rs:2190/2527, llvm/emitter.rs:169/191) — prediction,
  not verified.

## Blast radius (grep evidence)
- 45 sites compare find/index_of results raw (`>=0`/`==-1`).
- 429–1609 sites coalesce via `??` — silently take the nil branch when the true
  answer is 3 (production compiler .spl code incl. linker/backend).

## Representation finding (2026-07-22, MIR-dump-proven)
`T?` for primitives is NOT a union/enum: it lowers as `HirType::Pointer{inner:T}`
— a nullable-pointer optimization where the "pointer" IS the raw primitive and
nil is the fake pointer 3 (`hir/lower/expr/control.rs:554` documents this). The
lane is internally CONSISTENT raw: arithmetic, `??` (rt_unwrap_or_self
passthrough), if-val (direct Store copy — a separate HIR pattern path from
`??`), and function passing all agree on raw. The two defects are:
1. payload 3 == nil sentinel — UNSOUND BY CONSTRUCTION for full-range i64
   (no in-band sentinel can be sound; 3 is just badly placed).
2. generic print consumers assume TAGGED values — raw payloads misread as tag
   bits (the 1→"nil", 2→"0.0", 11→"true" garbage). Display defect only.

## Resolution (senior decision 2026-07-22)
- Defect 2 (print): FIX LANDED/IN FLIGHT — print lowering
  (mir/lower/lowering_expr_builtin.rs print special-case) routes
  Pointer{inner:primitive} args through nil-aware raw formatters
  (rt_opt_i64_to_string / rt_opt_bool_to_string), mirroring the existing
  rt_raw_i64_to_string 61-bit bypass.
- Defect 1 (payload-3 collision): DOCUMENTED LIMITATION, fix deferred. Full
  end-to-end tagging was designed and rejected for now: 7 site-groups across
  6+ files on the hottest lowering paths (Return needs new declared-type
  context threading; if-val and `??` are two independent paths; call-arg,
  Let/Assign, struct-field coercion sites all need wiring), it inherits the
  documented 61-bit BoxInt truncation, and the seed is bootstrap-only by repo
  policy. An earlier boundary-boxing spot-patch was PROVEN WRONG (`??` does
  not unshift). If/when fixed properly: retire the flat Pointer representation
  for primitive optionals in favor of the tagged scheme, using the make_opt
  matrix + arithmetic-after-unwrap + optional-chain + double-tag probes in the
  session record as the regression gate.
- Practical guidance until then: on seed-engine binaries, any `i64?` API can
  return nil when the true answer is exactly 3 (e.g. index_of match at
  position 3). Prefer `>= 0` sentinel-style APIs or add +1 offsets in critical
  paths; the self-hosted engine must be checked for the same representation
  before the same trust is extended (verification pending).

## Related prior filings (same family)
- native_i64opt_some0_collapses_to_nil (the 0-sentinel ancestor)
- seed BoxInt <<3 enum heap-handle mangling (stage4 wall)
- interpreter quirk ".? on 0-i64 → false" — likely the same lane, old sentinel

## Re-verification 2026-08-07 — STILL OPEN, shared Dict/list decode fixes did NOT cover this

Checked whether the 2026-08-07 Dict/list `.get()` decode fixes
(`native_dict_get_struct_value_corrupt_option_2026-07-27.md`,
`list_get_returns_tag_boxed_value_shifted_left_3_2026-07-28.md` — both landed
in `expr_dispatch.spl`'s runtime-array/struct element decode paths, e.g.
`elem_struct_name`/`elem_is_runtime_array` gating around
`decode_runtime_value`) also closed defect 1 here. They do not: those fixes
are about decoding boxed *container element* words (list/dict slot values);
this defect is the flat, non-boxed `i64?` scalar lane
(`HirType::Pointer{inner:i64}`) itself, a structurally different lowering
path with no shared call site. `git diff origin/main -- src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
is empty (no local drift) — confirms the file matches origin and this probe
reflects the current landed state, not a WIP edit.

Minimal repro (`val a: i64? = 3; val b: i64? = nil`), run via
`bin/simple run` (the deployed `bin/release/x86_64-unknown-linux-gnu/simple`,
which prints the "bootstrap seed only" banner — this is the seed's Cranelift
JIT, confirmed engaged via visible `cranelift_jit`-style IR dump in the run
log; the pure-Simple self-hosted binary was NOT separately re-checked this
session):

| expression | JIT (seed, default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|
| `a == nil` (a=3) | `true` — WRONG | `false` — correct |
| `u = a ?? -1; u == 3` | `false` — WRONG (value lost) | n/a, interpreter already correct |
| `u = a ?? -1; u == -1` | `true` — WRONG (`??` itself takes the nil branch) | n/a |
| `b == nil` (b=nil) | `true` — correct (coincidental) | `true` — correct |
| `v = b ?? -1; v == -1` | `true` — correct | `true` — correct |

Disambiguation note: an initial probe that `print`-interpolated `a ?? -1`
directly showed `<value:0xffffffffffffffff>` for BOTH the `a` and `b` cases,
which looked like a separate print/interpolation defect. Following up with
non-interpolated equality checks (`u == 3`, `u == -1`) proved the `??`
operator itself — not just its text formatting — resolves `Some(3)` to the
`-1` default, i.e. this is exactly defect 1 as already documented above, not
a sibling of the interpolation-only `jit_array_oob_read_leaks_raw_rt_nil_sentinel_2026-08-07.md`
gap. That doc's raw-`3`-prints-as-text symptom is unrelated here since our
`a`'s true payload (3) is being LOST, not printed verbatim.

Verdict: defect 1 (payload-3 collision) is CONFIRMED STILL OPEN on the JIT
lane, unchanged from the 2026-07-22 root-cause finding and the 2026-07-24
re-confirmation. The interpreter lane remains correct. No code was changed
here per the standing senior deferral ("an earlier boundary-boxing spot-patch
was PROVEN WRONG... do not re-attempt"); this is a status re-confirmation
only. Regression spec (interpreter-lane only, does not exercise the JIT
lane where the defect actually lives — see caveat in the spec docstring):
`test/01_unit/language/option_i64_value3_sentinel_spec.spl`.

## Re-verification 2026-08-08 — STILL OPEN; new tag-disjointness evidence does NOT apply here

Triggered by a new finding elsewhere in the runtime (used to correct
`doc/07_guide/language/dict_native_pitfalls.md`): `src/runtime/runtime_native.c`
defines disjoint tag classes — `RT_VALUE_TAG_SPECIAL 0x3` (:98),
`RT_VALUE_SPECIAL_NIL 0x0` (:99), `rt_core_nil() = (0<<3)|3 = 3` (:1553-1554,
`rt_core_from_special` at :1550 does `(payload << 3) | tag`). Under that
general/boxed/ANY tagged-value scheme, `raw == 3` IS a tag-safe nil check: a
genuine payload can only collide if its own shifted+tagged encoding
coincidentally equals 3, which cannot happen for a legitimately-tagged value
(heap `TAG_HEAP=0x1`, float `TAG_FLOAT=0x2`, and a tagged int/special payload
of exactly 0 shifted with tag 3). This raised the question of whether the
i64? sentinel-3 defect was actually misdiagnosed the same way.

It is not. Checked the representation directly rather than by analogy:

- `src/compiler_rust/compiler/src/hir/lower/expr/control.rs:1845-1850` (comment
  at the `??` lowering site) states explicitly: "the runtime nil sentinel IS
  the raw integer 3 ... emitting a runtime `expr != nil` check on a raw scalar
  turns the real value 3 into the default." This is the compiler's own
  admission that the i64? lane does NOT go through the tag-encode step at all.
- `src/compiler_rust/compiler/src/mir/lower/lowering_expr_literal.rs:44-53`
  (`lower_nil_expr`) confirms it structurally: MIR lowers the `nil` literal to
  `MirInst::ConstInt { dest, value: 3 }` — a bare constant `3`, not a call
  through `rt_core_from_special`/`rt_core_nil()` and not a `(payload<<3)|tag`
  encode. Every `T?` (`HirType::Pointer{inner:T}`) equality/coalesce/if-val
  check against `nil` is therefore comparing the RAW machine i64 against the
  literal `3`, on a domain (full-range `i64`) that was never tagged in the
  first place.

So the two representations only *share a bit pattern*, not a scheme: the
general/boxed value type reserves bit-pattern 3 inside a real 3-bit tag
namespace where collisions are provably excluded; the flat `i64?` lane reuses
the same numeral as a bare sentinel on an untagged domain, where a payload of
exactly 3 is bit-for-bit indistinguishable from nil by construction. The new
evidence that rescued the f64 dict case (`dict_native_pitfalls.md`) does not
generalize here — it is a different lane with a different (absent) tagging
step, confirmed from the lowering source, not inferred by analogy.

Empirical re-confirmation (seed JIT, `bin/simple run`, banner-confirmed seed
engine; probes kept one-per-file per the harness rule to avoid whole-program
interpreter demotion), scratch files under
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/5b123a16-9921-4156-9711-79d7b39487c0/scratchpad/probe_{eqnil,coalesce,ifval}_{2,3,4}.spl`
and `probe_eqnil_nil.spl`:

| value | `a == nil` (JIT) | `a ?? -1` (JIT) | `if val x = a` (JIT) | interpret (`== nil`) |
|---|---|---|---|---|
| 2 | false (correct) | `0.0` (garbage, not nil-collision) | `IFVAL=0.0` (garbage) | false |
| **3** | **true — WRONG** | `<value:0xffffffffffffffff>` (default branch taken, payload lost) | **IFVAL_NONE — WRONG** (unwrap skipped) | false (correct) |
| 4 | false (correct) | `<value:0x4>` (garbage, not nil-collision) | `IFVAL=<value:0x4>` (garbage) | false |
| nil | true (correct) | n/a | n/a | true |

This exactly reproduces the 2026-08-07 matrix and the original 2026-07-22
`make_opt` matrix: values 2/4 show the separate, already-documented tag-misread
display defect (defect 2) but remain distinguishable from nil; only 3 collides
with nil across all three consumer forms (`==`, `??`, `if val`). Interpreter
lane (`SIMPLE_EXECUTION_MODE=interpret`) stays clean at all four values.

Regression spec re-run: `bin/simple test
test/01_unit/language/option_i64_value3_sentinel_spec.spl` → `Results: 5 total,
5 passed, 0 failed` (interpreter lane only, as documented in the spec's own
caveat — it does not exercise the JIT lane where the defect lives).

**Verdict: STILL LIVE.** The recorded root cause (unsound in-band sentinel on
an untagged flat `i64?`/`Pointer{inner:i64}` lane) is CONFIRMED CORRECT, now
directly from the MIR lowering source (`lowering_expr_literal.rs:50`) rather
than only from behavioral probing. The new tag-disjointness evidence from the
runtime's boxed-value scheme is real but inapplicable — it describes a
different, already-tagged representation that this lane never uses. No code
changed, per the standing senior deferral against a narrow spot-fix.

## Re-verification 2026-08-09 — STILL OPEN; no code change (standing deferral honored)

Re-ran the full `==nil`/`??`/`if val` triage on `origin/main`'s deployed seed
JIT (`bin/simple run`, banner-confirmed seed engine) plus a wider single-value
sweep than the prior sessions covered, to rule out the collision having moved
to a different sentinel:

| value | `a == nil` | note |
|---|---|---|
| -1 | false (correct) | |
| 0 | false (correct) | |
| 1 | false (correct) | |
| 2 | false (correct) | |
| **3** | **true — WRONG** | payload lost, same as all prior sessions |
| 4 | false (correct) | |
| 5 | false (correct) | |
| 11 | false (correct) | |
| 100 | false (correct) | |
| nil | true (correct) | |

Also re-confirmed the `??`/`if val` forms on payload 3 specifically
(`a ?? -1` → `<value:0xffffffffffffffff>`, default branch taken; `if val x = a`
→ `IFVAL_NONE`, unwrap skipped) — identical to the 2026-08-08 matrix. Only the
single value 3 collides across the swept range; no other value (including the
prior sentinel candidate 0, and 11 which is `3 mod 8` — a plausible tag-bit
alias) reproduces it, confirming the collision is exactly and only the bare
constant 3 emitted by `lower_nil_expr` (`lowering_expr_literal.rs:50`), not a
wider tag-class collision.

**No code change made.** Per the standing senior deferral recorded above, a
narrow spot-patch to the flat `i64?` lane was designed and **proven wrong
twice** (boundary-boxing doesn't unshift `??`); the real fix is the deferred
7-site-group/6+-file retag (Return type-context threading, if-val, `??`,
call-arg, Let/Assign, struct-field coercion), which also inherits the 61-bit
BoxInt truncation caveat and touches the hottest lowering paths shared by the
bootstrap pipeline. Re-attempting a narrow fix here — especially while several
other agents are concurrently editing compiler lowering files this session —
would repeat the already-rejected approach and risks regressing `print`/`??`
for all values, per the explicit prior-session finding. This entry is a
status re-confirmation only, landed as a doc-only change.

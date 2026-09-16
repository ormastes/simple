# Pure-Simple `list`-param element read: correct for int content, SIGSEGV on non-int content (2026-08-08)

Assignment: implement, in pure Simple, the fix for the seed-documented
`<<3` untyped-`list`-element-read bug
(`doc/08_tracking/bug/untyped_list_element_read_seed_rootcause_2026-07-30.md`).
Per that bug's own root-cause: `list` resolves to `HirType::Array{element: ANY}`,
and the seed's `needs_int_unbox` conservatively declines to unbox an
`ANY`-typed element because it cannot statically prove the content is
integer — the safe, principled choice, at the cost of a wrong (`value*8`)
read for the common all-integer case.

## Pure-Simple counterpart: same type resolution, different (also unsafe) decode default

`src/compiler/20.hir/hir_lowering/types.spl:671` — bare `"list"` resolves
identically to the seed: `case "list": HirTypeKind.Array(HirType(kind:
HirTypeKind.Any, span: span), nil)`.

`src/compiler/50.mir/_MirLowering/function_lowering.spl:672-673` —
`lower_type` collapses `HirTypeKind.Any` unconditionally to `MirType.i64()`
(no ANY/erased MIR type exists; i64 is "the compiler's existing
pointer-width type-erasure slot").

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `lower_index_expr`
(~line 1522) then derives `result_type` for a `list`-typed parameter's
element read from that same `Any -> i64` lowering (via the base-local's HIR
type, `HirTypeKind.Array(element_type,_) => result_type = self.lower_type(element_type)`,
~line 1659-1661), and the shared `decode_runtime_value` (~line 803) branches
purely on `result_type`'s kind: `mir_type_is_integer(result_type)` is true
for i64, so it unconditionally takes the integer-unbox arm (`>>3` shift +
cast, line 806-812) — the exact decode the seed declines to emit for `ANY`.

**Net effect: the two compilers made opposite unsafe defaults for the same
underspecified case.** Seed: never unbox ANY-typed elements (safe against
corruption, wrong value for the dominant int-content case). Pure-Simple:
always unbox ANY-typed elements as if they were i64 (correct for the
dominant int-content case, but a raw arithmetic shift-right of a genuinely
boxed/tagged non-integer value — exactly the type-confusion the seed's
comment warns is "not just a wrong-value bug; it can hand later code a
garbage address").

## Verification (native-build, `bin/simple` deployed seed as host interpreter)

1. **Marker confirmed live**: an unconditional `eprint` placed at the top of
   `lower_index_expr` fired twice under `native-build` of
   `test/fixtures/untyped_list_element_shift/main.spl` (2 `l[i]` index
   sites in the fixture) — this lowering path is genuinely reached, not
   dead code on the native-build lane.
2. **Int-content case (the documented bug's exact repro) is already
   correct** under native-build — no seed-side fix needed here:

   | call | native-build result | expected |
   |---|---|---|
   | `get_via_typed_param(buf, 0/1)` (`[i64]` control) | `5, 7` | `5, 7` |
   | `get_via_list_param(buf, 0/1)` (`: list` param) | `5, 7` | `5, 7` |

   (Contrast with the seed's JIT lane, which still reproduces `40, 56` per
   the 2026-08-08 re-verification in the original bug doc — unchanged,
   not touched by this pass.)
3. **Mechanism confirmed, not just outcome**: a second marker at the
   `runtime_array`/`decode_runtime_value` call site showed
   `runtime_array=true`, `is_tuple_base=false`,
   `result_type_is_int=true` for both index reads — i.e. the read takes the
   `rt_array_get` + `decode_runtime_value` path and hits the integer-unbox
   arm specifically, not an unrelated raw GEP/load bypass.
4. **New defect surfaced**: a heterogeneous-content probe (`: list` param
   backed by a `[text]` array, `["ab", "cd"]`) built and ran clean
   (`rc=0` native-build), then **SIGSEGV'd at runtime**
   (`[simple-runtime] Fatal: SIGSEGV at address 0xc226ca01a54`) on the first
   `l[i]` read — the tagged string-handle word gets arithmetic-shifted as
   if it were a boxed integer, producing a garbage pointer that later code
   dereferences. This is strictly worse than the seed's wrong-value bug: a
   crash instead of a bad number.

## Why this pass does not land a fix

Fixing the segfault without reintroducing the seed's wrong-value bug
requires exactly the "no small, safe, contained change" machinery the
original bug doc already identified as out of scope for a single pass: a
runtime-tag-dispatched decode invoked per-element at the point of
consumption (inspect the boxed value's tag bits at runtime, the way the
interpreter already does, rather than deciding statically), or call-site
monomorphization of `list`-typed parameters. Both are new compiler
capabilities, not a local edit to `lower_index_expr`/`decode_runtime_value`.
An unconditional-unbox-as-int default (today's pure-Simple behavior) is not
that fix — it happens to paper over the seed's specific `5/7`-int repro
while creating a crash on any non-int `list` content, which is a worse
regression in the general case per the original bug doc's own caution ("a
plausible-looking 'always unbox' patch would silently corrupt ... in
exchange for fixing the ... dominant cases").

## Fence disposition

`scripts/check/check-untyped-list-element-shift.shs` is left unchanged: it
exercises the seed's `bin/simple run` JIT lane specifically (not
native-build), which this pass did not touch and which remains
KNOWN-OPEN exactly as before. No native-build fence is added this pass
either — asserting "the int case works" would enshrine the same unsafe
default this doc documents as a latent SIGSEGV, and a fence for the SIGSEGV
itself would just pin a known crash without a real fix behind it. Recommend
this doc as the next-session's basis for either (a) a scoped runtime-tag
dispatch limited to the consumption sites that need it, or (b) at minimum a
compile-time diagnostic when a `: list`/`ANY`-typed array element read
feeds an arithmetic/bitwise context, so the crash becomes a compile error
instead of a runtime SIGSEGV.

## Scratch probes (not committed)

- `test/fixtures/untyped_list_element_shift/main.spl` — pre-existing fixture,
  untouched, byte-identical.
- Heterogeneous-content probe used only from scratch:
  `fn get_via_list_param(l: list, i: i64) -> text: return l[i]` /
  `main(): var buf: [text] = ["ab", "cd"]; get_via_list_param(buf, 0/1)`.
  Not added to the tree (would need its own SIGSEGV-tolerant fence
  machinery this pass doesn't build); reproduce by pasting into a scratch
  dir and running the `native-build` invocation in the Guide section of the
  originating task.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: ALREADY-FIXED BY CONTENT (the SIGSEGV half), in the runtime rather than in 50.mir.**

`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:848-861` no longer emits a
bare `>> 3` for the I64/U64 erased-element case; it routes through
`rt_value_as_int_wide`. That function, at `src/runtime/runtime_native.c:2206-2226`,
now returns a HEAP-tagged handle unchanged instead of shredding it
(`if ((((uint64_t)value) & 0x7ULL) == RT_VALUE_TAG_HEAP) return value;`), and its
comment names the sibling bug `native_empty_dict_text_value_sigsegv_2026-07-20`
and the exact strcmp SIGSEGV signature. Separately,
`scripts/check/check-untyped-list-element-shift.shs` was executed on 2026-08-17:
rc=0, `PASS — interpreter reference lane correct: typed=[5,7], list-param=[5,7]`,
plus a `KNOWN-OPEN` line reporting `list0=40 list1=56` (value*8). That KNOWN-OPEN
belongs to the SEED lane and is tracked by
`untyped_list_element_read_seed_rootcause_2026-07-30.md`, not by this pure-Simple
doc.

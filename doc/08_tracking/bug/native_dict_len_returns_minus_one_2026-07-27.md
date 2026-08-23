# Bug: `Dict.len()` returns -1 in native codegen (locals and struct fields, empty or populated)

- **Date:** 2026-07-27
- **Status:** NOT REPRODUCIBLE as of `8fdc21c67b5` (2026-08-01) — see "Re-measured" below
- **Area:** native codegen — MIR `.len()` method lowering, dict receivers
- **Severity:** high — silently defeats any `len() == 0` / `len() < 0` guard; caused a multi-hour misdiagnosis during stage-4 bootstrap debugging
- **Found by:** isolated native-codegen probe (Probe A), one-binary build

## Re-measured 2026-08-01 — does not reproduce

Native ELF built from a clean `origin/main` at `8fdc21c67b5` (LLVM backend,
`native-build --entry`, verified by running the produced binary directly):

```
local_len=2       <- Dict<text,i64> local, two entries
param_len=2       <- same dict passed as `fn f(d: Dict<text,i64>)`
```

Both routes report the true entry count. The `rt_len` -> `rt_string_len`
fallback described below is therefore no longer being taken for these two
receiver shapes — `local_is_runtime_dict` now recovers dict-ness for both the
local and the parameter (the parameter case was the `native_dict_param_no_dictness`
follow-up already landed in `method_calls_literals.spl`).

**Still unmeasured:** the STRUCT FIELD receiver from the original Probe A.
Module-level `struct` declarations still make `native-build` fail with
`MIR module has no functions` (the separate native-build defect noted in the
`.get()` miss bug doc), so that row could not be re-run. Do not close this bug
on the strength of the two rows above alone.

## Summary

`Dict<K, V>.len()` returns **-1** under native codegen, both when the
receiver is a local variable and when it is a struct field, and regardless of
whether the dict is empty or populated with real entries. Correct behavior
would be `0` for an empty dict and the true entry count for a populated one.

## Evidence (Probe A)

Native one-binary build, `Dict<text, i64>` populated as `{"x": 7, "y": 9}`,
probed both as a local and as a struct field:

```
local: len=-1 keys=2 getx=56 has_x=true miss=-77
field: len=-1 keys=2 has_x=true
field getx_isnil=false val=56
field miss_isnil=true val=-77
```

`.len()` returns **-1** in both cases, despite `.keys()` correctly reporting
`2` entries for the same dict. (`.get()`'s own undecoded-value symptom on
this same probe is a separate bug — see "Related" below.)

## Root-cause pointer

`.len()` / `.length()` lowering:
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1287+`
(`if (method == "len" or method == "length") and args.len() == 0:`). Per the
companion root-cause analysis in
`doc/08_tracking/bug/native_nil_dict_get_phantom_option_rootcause_2026-07-27.md`
("Why `.len()` returns -1"), there are two routes:

- A **statically-typed** dict receiver routes to `rt_dict_len` and returns
  the correct count (or `0` for a truly nil/invalid receiver).
- An **untyped/erased** receiver — the receiver's local has no MIR type
  recognized as a dict by the `.len()` lowering's own resolution logic — falls
  through to the generic `rt_len` path, which gets rewritten to
  `rt_string_len` when the local isn't a known runtime array
  (`method_calls_literals.spl` ~1355-1369). `rt_string_len` on a non-string,
  non-heap handle returns **-1** unconditionally
  (`src/runtime/runtime_native.c:1741-1745`):

  ```c
  int64_t rt_string_len(int64_t string) {
      RtCoreString* s = rt_core_as_string(string);
      if (s) return (int64_t)s->len;
      return string >= 0x10000 ? (int64_t)strlen((const char*)(uintptr_t)string) : -1;
  }
  ```

Probe A shows this **erased fallback path is taken even for a directly
declared `Dict<text, i64>` local** (not just for genuinely nil/erased
receivers) — the same receiver's `.keys()` call in the same probe correctly
identifies it as a dict (returns `2`), so the dict-ness information exists
somewhere in the lowering context but is not being consulted by the `.len()`
arm's own type resolution the way `.keys()`'s is. This needs the same kind of
value-type-resolution audit noted in the companion `.get()` bug doc — `.len()`
is a third site (alongside `.get()` and `d[k]`) with its own, apparently
narrower, dict-receiver detection.

## Danger

This silently defeats **any** `d.len() == 0` or `d.len() < 0` guard written
against the natural assumption that `.len()` reports a dict's true size. It
is not a crash — it is a silent semantic corruption that only surfaces as
downstream misbehavior.

Concretely, during the stage-4 bootstrap segfault investigation on
2026-07-27, a `functions.len() < 0` heuristic (used in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` to detect
"partial" header-only modules) **fired on every module** because
`.len()`'s -1 result is indistinguishable, at that call site, from a
genuinely partial module — 35,483 times in one stage-4 run. This produced
hours of misdiagnosis before the true defect (the corrupt `.get()` decode on
struct-valued dicts, `native_dict_get_struct_value_corrupt_option_2026-07-27.md`)
was isolated by direct probing. The `functions.len() < 0` mitigation
happens to still work as a *coincidental* guard today (both the "genuinely
partial module" case and the "erased .len() fallback" case yield a negative
number), but that is fragile: any future receiver shape that lands in the
erased fallback and is NOT a partial module would trip the same false
"partial" classification.

## Suggested fix

Route `.len()` for dict receivers through `rt_dict_len` using the **same**
dict-receiver detection that `.keys()` / `.get()` / `d[k]` use (a runtime
type/tag check, or the same `local_is_runtime_dict` helper used by the index
lowering in `expr_dispatch.spl:971`), instead of falling back to the generic
`rt_len` → `rt_string_len` chain for any receiver whose MIR-local type wasn't
statically resolved. `rt_string_len` returning `-1` for a non-string handle
(`src/runtime/runtime_native.c:1744`) is itself a reasonable fail-closed
default for *string* receivers and should not be changed — the fix belongs
in `.len()`'s dict-receiver routing, not in `rt_string_len`.

**Do not** change `rt_string_len`'s `-1` return value as part of fixing this:
per the companion root-cause doc, the currently-landed stage-4 mitigations in
`module_lowering.spl` key on `functions.len() < 0`; changing `-1` to `0`
before those guards are relaxed to `<= 0` would silently disarm them.

## Related

- `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md`
  — the `.get()` corrupt-Option bug found on the same probe (Probe A/B/C);
  the true root cause of the stage-4 segfault this `.len()` bug helped
  misdiagnose.
- `doc/08_tracking/bug/native_nil_dict_get_phantom_option_rootcause_2026-07-27.md`
  — prior root-cause analysis of the -1 route (nil-receiver case) and the
  `rt_string_len` fallback mechanics quoted above.
- `doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`
  — the `functions.len() < 0` mitigation that this bug's -1 result happens to
  satisfy coincidentally.
- `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1287+` —
  `.len()`/`.length()` lowering.
- `src/runtime/runtime_native.c:1741-1745` (`rt_string_len`), `:4825+`
  (`rt_dict_len`).

## Re-measured 2026-08-23 — the STRUCT FIELD row finally has evidence, and it is RED

The row this record explicitly left open ("Still unmeasured: the STRUCT FIELD
receiver from the original Probe A ... Do not close this bug on the strength of
the two rows above alone") is now measured, at scale, by the bootstrap itself.

**Observation.** Stage 3 at `6c78a408f8d` failed at step 1/6 with:

```
Module surface registry graph lost after phase 2 retention: surface
declaration-authority arrays invalid: index=0 count=26; surfaces=691
names=946 indices=946 dict=-1
```

`dict=-1` is `retained_surfaces.index_by_name.len()` — a `Dict<text, i64>`
read as a STRUCT FIELD (`driver_source_pipeline_parsing.spl`). It is the
clause `authority_count != ...index_by_name.len()` in
`module_surfaces_frozen_alignment_error` that actually fired: `names.len()`
was 26 and the same index's `index_by_name.len()` was -1.

An independent measurement in the same lane (recorded in the comment on
`module_surfaces_rebuild_declaration_authority_carriers_error`,
`module_surface_registry.spl`) is decisive about what -1 does and does not
mean here: a `Dict<text, i64>` **freshly allocated and filled with 26 entries
moments earlier reports `len() == -1` while every one of its keys answers
`contains_key` correctly**. The entries are live; only `len()` lies.

So this is NOT the documented `.get()`-miss family and NOT a regression of the
2026-08-01 routing fix / `7e83e92ce31` — both of those were verified on LOCAL
and PARAMETER receivers (and, for `7e83e92ce31`, via JIT). It is the third,
never-measured receiver shape of this very record, reached AOT.

**Note for `.claude/rules/code-style.md`.** That file states `Dict.len()` "is
now safe to call directly". That is over-broad: it is safe for the two rows
this record re-measured green, and false for the struct-field row above.

## Cross-implementation verdict (both directions, per user directive)

Static source evidence, `origin/main` 2026-08-23:

| half | `.len()` on an unprovable receiver | result on a dict handle |
|---|---|---|
| C runtime `rt_len` (`src/runtime/runtime_native.c:2976`) | string arm, array arm, `else 0` — **no dict arm** | `0` |
| Pure-Simple MIR (`50.mir/_MirLoweringExpr/method_calls_literals.spl:1853-1866`) | picks `rt_dict_len` only when `local_is_runtime_dict` proves it; otherwise `rt_len`, then **rewrites `rt_len` -> `rt_string_len`** unless the local is a known array | `rt_string_len` (`:2651`) fails `rt_core_as_string`, then does `strlen()` on the DICT'S OWN HEAP MEMORY when `handle >= 0x10000`, else returns **`-1`** |
| Rust seed LLVM codegen (`codegen/llvm/functions.rs:2528`, `functions/calls.rs:2064,2234`) | emits plain **`rt_len`**; `rt_dict_len` only for a statically-known `Dict` (`functions.rs:2991`) | `0` (no `rt_string_len` rewrite) |

**Twin FOUND — and the two halves are wrong DIFFERENTLY.** Pure-Simple
degrades to `rt_string_len` (a `strlen` over foreign heap, i.e. undefined
behaviour, or `-1`); the seed degrades to a silent `0`. Neither reports the
true count. `local_is_runtime_dict` (`expr_dispatch.spl:353`) recovers
dict-ness for locals and for parameters (via the registered MIR type) but not
for a FIELD READ, which is exactly why the struct-field row is the one that
stayed red.

**Common root:** `rt_len` in the C runtime has no dict arm. This is the same
defect class already filed as
`doc/08_tracking/bug/stage3_dict_clear_no_dict_branch_in_rt_clear_2026-08-17.md`
(`rt_clear` missing its dict branch) — a generic runtime accessor whose
dispatch enumerates string and array and silently drops dict.

**Open discrepancy, stated rather than papered over.** The observed value was
`-1`, but the failing binary was stage 2, emitted by the Rust seed, whose
codegen path predicts `0`. Either the seed has a second `.len()` route that
reaches `rt_string_len` (`functions/calls.rs:445`, `functions.rs:2878/2895`,
and `("String"|"string","len") => "rt_string_len"` at `functions.rs:2967` are
the candidates), or the field read is typed as `String` at HIR. This has NOT
been resolved by execution and must not be asserted either way.

## Status of the phase-3 blocker (separate from this defect)

The bootstrap failure above is **already fixed on `origin/main`** — and by
working AROUND this bug, not by fixing it:

- `948632ef324` removed the `authority_count != ...index_by_name.len()` clause
  from `module_surfaces_frozen_alignment_error` and replaced it with a
  functional probe of `module_surface_declaration_authority_lookup` over every
  key. Verified by `git show 6c78a408f8d:...registry_index.spl` — the clause is
  present at the failing commit (line 234) and absent now.
- `a6f72fb3882` + `driver_source_pipeline_parsing.spl:493-499` add and wire
  `module_surfaces_rebuild_declaration_authority_carriers_error`, which
  rebuilds each carrier after teardown and, per its own comment, deliberately
  judges viability by a full key sweep and "never by `len()`".

So `Dict.len()` on a struct field remains broken; the compiler has stopped
asking it. This record stays OPEN.

## Guard-disarm hazard before changing what -1 becomes

Per this record's own tail, live mitigations key on `functions.len() < 0`
(`50.mir/_MirLowering/module_lowering.spl`, and
`hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`). Adding a dict arm
to `rt_len` turns some `-1`/`0` results into true counts and can silently
disarm those guards. Audit every `len() < 0` / `len() == -1` guard in the same
change. The upstream probe-based checks described above do not use `len()` and
are unaffected.

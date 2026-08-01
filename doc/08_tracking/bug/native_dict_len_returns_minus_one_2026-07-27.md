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

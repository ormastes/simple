# String-only MIR arm is receiver-blind for `find`/`rfind`: array receiver silently returns -1

**Date:** 2026-08-01
**Severity:** high — silent wrong answer (a present element reports "not found")
**Status:** FIXED (this change) for `find`/`rfind`; the wider receiver-blind
class remains OPEN — see
`codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`
**Component:** `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`
(pure-Simple MIR lowering), string-method dispatch arm

## Mechanism

The string-only lowering arm at `method_calls_literals.spl:1963` fires for the
name set `trim/strip/lower/to_lower/to_upper/split/replace/rfind/find/contains/
parse_f64` and emits `rt_string_*` runtime calls. It is guarded by
`and not contains_recv_is_array`, an exclusion whose stated purpose is to keep a
positively-known array/slice receiver OUT of the string arm so it falls through
to the LOUD unresolved-method build failure.

The guard was **consumed by the whole arm but computed for only one name**. At
the pre-fix `:1868`:

```
if method == "contains" and args.len() == 1 and resolution_is_unresolved and ...
```

So for `method == "find"` or `"rfind"` the flag stayed `false` regardless of the
receiver. Dispatch decided by **method name + arity alone**, never consulting the
receiver type — receiver-blind in exactly the sense that produces a plausible
wrong answer rather than an error.

Downstream, `find` maps to `rt_string_find` (`:2008`). Passing an array handle
there reaches `rt_core_as_string(value)` in
`src/runtime/runtime_native.c:3173`, which returns NULL for a non-string, and
the function returns **-1**. `-1` is also the legitimate "needle not present"
result, so the miscall is indistinguishable from a genuine miss at every call
site: `arr.find(x)` reports "not found" for elements that ARE present.

This is the same failure shape already documented for `contains` (silent
`false`), and the sibling two-arg `index_of` arm at `:1907` already computes its
own `tf_recv_is_array` probe. `find`/`rfind` were the un-swept members of that
family — a mitigation gap, not a clean regression: the guard was born
`contains`-only. (Git history through this path is polluted by the
`beea94b72ce` / `118c636ead8` tree wipes and their restores, so no honest bisect
date is available.)

## Fix

Extend the probe's computation to the whole arity-1 search family so the flag is
populated for every name the arm actually serves:

```
if (method == "contains" or method == "find" or method == "rfind") and args.len() == 1 and ...
```

Both existing receiver checks (the `HirTypeKind.Array/Slice` static check and
the `local_is_runtime_array` runtime-local probe, which is restricted to
`Var`/`NamedVar` receivers and therefore side-effect-free to repeat) now apply
to `find`/`rfind`. An array receiver is excluded from the string arm and fails
loudly on the unresolved path instead of returning -1.

## Blast radius

Owned `.spl` sources (excluding `**/vendor/**`), call sites that reach the
affected names:

| method | call sites | pre-fix behaviour on an array receiver |
|---|---|---|
| `find` | 578 | silent `-1` ("not found") |
| `rfind` | 75 | silent `-1` |
| `contains` | 6,484 | already guarded (silent `false` before its 2026-07-xx fix) |

Only the subset whose receiver is an array/slice AND whose resolution is
`Unresolved` at this lowering point is affected; the counts are the upper bound
on reachable sites, not confirmed victims. Typed/resolved receivers never enter
this arm.

## What was measured, and what was NOT

**Engine measured: the Rust seed** (`src/compiler_rust/target/bootstrap/simple`),
both the JIT (`run`) and the tree-walk interpreter (`SIMPLE_NO_JIT=1`, valid
only after `b7151d94114`).

Probe (`push` x3 with content check; `find` for a needle at a **nonzero** index
plus a known-absent needle) on typed receivers: **both engines correct**
(`push_len=3`, contents intact, `find("cd")==2`, `find("zz")==-1`). The probe is
non-vacuous — an earlier run with a deliberately wrong expected index reported
`FAILS=1`, proving it discriminates rather than passing by construction.

**`rt_array_push` silently returning `false` did NOT reproduce.** Pushes were
not dropped on either seed engine. `rt_array_push` returning `0`
(`runtime_native.c:4527`) is its own null-receiver guard
(`rt_core_array_ptr(a) == NULL`), i.e. receiver-type-*aware* failure, not an
allowlist rejection. A symmetric hazard does exist at `:2553`
(`if method == "push" and args.len() == 1:` emits `rt_array_push` for any
Unresolved receiver, name+arity only) — a non-array receiver there would take
the NULL guard and drop the append silently. **Unverified**: left unfixed and
recorded here rather than patched speculatively.

The defect fixed here is in the **pure-Simple** lowering lane, which `simple
run`/`simple test` do not execute (they delegate to the Rust seed child), and
that lane cannot self-host at HEAD. So this fix is **verified by construction
and code reading, not by an executed spec.** That gap is stated deliberately.

## Correction to the original report

The reported framing — "an allowlist rejects a legitimate call, failing CLOSED"
— is inverted. No allowlist rejects a legitimate `arr.push()` or `str.find()`;
`push` and `find` are present in every such list. The real mechanism runs the
other way: a name-only list **forces** builtin dispatch onto a receiver whose
type was never checked, and the runtime's own type guard then returns its
failure sentinel (`-1` / `false`). The observable symptom matches the report;
the cause is receiver-blind over-inclusion, not exclusion.

# Native: d[k] on a fn-call-derived dict during keys() iteration returns 0

**Status:** Resolved 2026-07-15  **Found:** 2026-07-14 (iterators lane)  **Path:** native-build --entry
```simple
val d = make_dict()          # dict returned from a fn
for k in d.keys():
    total += d[k]            # was: native 0 ; now: correct sum == oracle
```

## Root cause

The call-result dict local *did* route `.keys()`/`d[k]` to
`rt_dict_keys`/`rt_dict_get` (its `MirType.Dict` return type was threaded). The
real defect was the **key type representation**: a dict literal records its key
type as `Opaque("str")`, but a dict from a function derives it via `lower_type`,
whose `Str` case produces the fat-pointer `Tuple([Ptr(U8), U64])` shape.
`decode_runtime_value` only un-tags `Opaque("str")`, so each `keys()` element (a
tagged heap-string handle) came back un-decoded and never matched in
`rt_dict_get`'s key comparison → every lookup returned 0.

## Resolution

`abde1838e3e4` (dictcallkeys lane): in the `.keys()`/`.values()` lowering,
normalize any string-shaped key/value MIR type (`mir_type_is_str`) to
`Opaque("str")` before stamping the result-array element type, so
`decode_runtime_value`'s existing `Opaque("str")` branch runs for a call-result
dict exactly as it does for a literal dict. Single file
(`method_calls_literals.spl`).

Verified native == oracle (sum 3) for the exact repro. Parity harness case
`dict_from_call_keys` is green in the `check-native-seed-parity.shs` gate.

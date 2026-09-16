# `Dict<i64, _>.keys()` yields text-typed keys: `+` concatenates instead of adding

**Date:** 2026-09-02 · **Status:** OPEN · **Severity:** high (silent wrong
arithmetic — no error, no warning, a plausible-looking wrong number)

## Provenance
HEAD `c80479229e2`, seed `src/compiler_rust/target/release/simple.exe`
md5 `286f66b8615dce0e0da788f0550c4008` (39,120,896 bytes),
`SIMPLE_EXECUTION_MODE=interpret`.

## Symptom

Summing the keys of an `i64`-keyed dict produces the TEXT concatenation of the
keys, not their sum. Nothing errors; the result is silently wrong.

```
var d: Dict<i64, bool> = {}
d[1] = true
d[2] = true
var t = 0
for k in d.keys():
    t = t + k
print(t)          # prints  012   -- expected 3
```

`012` is `0` (the accumulator's initial value) concatenated with `1` then `2`.

## Minimal reproduction

```
struct Item:
    label: text

struct Maps:
    items: Dict<i64, Item>

impl Maps:
    static fn empty() -> Maps:
        Maps(items: {})

fn probe():
    var m = Maps.empty()
    m.items[1] = Item(label: "a")
    m.items[2] = Item(label: "b")
    val ks = m.items.keys()
    print("keys={ks} len={ks.len()}")
    var total = 0
    for key in ks:
        print("key={key} total_before={total}")
        total = total + key
    print("field-dict total={total}")

    var d: Dict<i64, bool> = {}
    d[1] = true
    d[2] = true
    var t2 = 0
    for k2 in d.keys():
        t2 = t2 + k2
    print("local-dict total={t2}")

probe()
```

Measured output:

```
keys=[1, 2] len=2
key=1 total_before=0
key=2 total_before=01
field-dict total=012
local-dict total=012
```

## What this pins down

- It is **not** specific to struct fields: a plain local `Dict<i64, bool>`
  reproduces it identically (`local-dict total=012`). So this is not a
  member-access or construction problem.
- It is **not** a rendering artifact: `total_before=01` on the second iteration
  shows the accumulator is ALREADY textual after one step, so the wrong value is
  really stored, not merely printed oddly.
- `.keys()` itself LOOKS right: `keys=[1, 2] len=2` — the list prints
  numerically and has the right length. Only the arithmetic betrays the key's
  runtime type, which is why this can sit undetected.
- `+` is the operator that reveals it, because `+` is overloaded for text. An
  operator with no text overload would presumably error instead; not yet
  measured.

## Not yet measured
- Whether `-`, `*`, comparison, or use as an array index are equally affected.
- Whether `text`-keyed and `i64`-keyed dicts differ, or `.values()` is affected.
- Whether native codegen behaves the same as the interpreter here (this was
  measured on the interpreter only). Note the related open native-only Dict gaps
  in `doc/07_guide/language/dict_native_pitfalls.md`.
- Whether an explicit `key as i64` cast is a sound workaround.

## How it was found
While writing the generalization spec for
`doc/08_tracking/bug/mcp_native_build_post_mono_nil_contains_2026-09-01.md`.
An example that summed dict keys failed with `expected 012 to equal 3`. That
example was NOT weakened to hide the failure — it was recognised as a different
defect class (key TYPING, not field CONSTRUCTION), reduced to the local-dict
repro above, and filed here. The spec keeps an on-topic for-in example and
points at this record.

Related specs:
- `test/01_unit/compiler/50.mir/struct_collection_field_construction_contract_spec.spl`
- `test/01_unit/compiler/50.mir/mir_lowering_global_maps_initialized_spec.spl`

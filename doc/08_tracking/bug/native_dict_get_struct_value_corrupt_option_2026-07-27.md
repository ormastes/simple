# Bug: `Dict<K, StructValue>.get()` returns a corrupt Option on a HIT (native codegen); index read and `Some(index)` are correct

- **Date:** 2026-07-27
- **Status:** open
- **Area:** native codegen — MIR dict-method lowering (`.get()` vs `d[k]` decode divergence)
- **Severity:** high — was the true root cause of the stage-4 bootstrap segfault previously (wrongly) attributed to header-only/partial modules with nil decl dicts
- **Found by:** isolated native-codegen probes (A, B, C below), one-binary build

## Summary

`Dict<K, V>.get(k)` on a **valid, non-nil dict, on a HIT** returns a value that
is unsafe to use:

- For `V = i64`: the returned value is the **still-boxed, undecoded** integer
  (`raw`, not `raw >> 3`) — silently wrong, no crash.
- For `V` a struct type: the returned Option is non-nil and passes `!= nil`,
  but reading a field of the unwrapped value, or calling `.unwrap()` and then
  touching a field, **segfaults**.

Misses are correctly nil in both cases. `.keys()`, `.contains_key()`, and the
index-read form `d[k]` are **all correct** for the same dict/key. `Some(d[k])`
constructed manually round-trips correctly too. The defect is specific to the
`.get()` method's own decode step.

## Evidence

### Probe A — `Dict<text, i64>`, both as a local and as a struct field

Native one-binary build, dict populated as `{"x": 7, "y": 9}`:

```
local: len=-1 keys=2 getx=56 has_x=true miss=-77
field: len=-1 keys=2 has_x=true
field getx_isnil=false val=56
field miss_isnil=true val=-77
```

`.len()` returns **-1** (both local and field — tracked separately, see
"Related" below; NOT this bug). `.get("x")` returns **56 = 7<<3**, i.e. the
raw boxed representation of `7` under the runtime's `(value<<3)|TAG_INT`
encoding — the `>>3` unboxing step never ran. `.keys()`, `.contains_key()`,
and the index read `d["x"] == 7` are all correct. A miss (`"z"`, say) correctly
yields nil (`miss=-77` is the caller's own sentinel value for "nil", not a
runtime value).

### Probe B — `Dict<text, StructValue>` (the decisive probe)

```simple
struct Tr:
    name: text
    n: i64

struct Holder:
    traits: Dict<text, Tr>

fn main():
    var d: Dict<text, Tr> = {}
    d["Read"] = Tr(name: "Read", n: 5)
    val h = Holder(traits: d)
    print "has_hit={h.traits.contains_key("Read")} has_miss={h.traits.contains_key("Nope")}"
    val hit = h.traits.get("Read")
    print "get_hit_isnil={hit == nil}"
    val miss = h.traits.get("Nope")
    print "get_miss_isnil={miss == nil}"
    val idx = h.traits["Read"]
    print "idx name={idx.name} n={idx.n}"
    if hit != nil:
        print "hit unwrap name={hit.unwrap().name} n={hit.unwrap().n}"
```

Output:

```
has_hit=true has_miss=false
get_hit_isnil=false
get_miss_isnil=true
idx name=Read n=5
```

...then **SEGFAULT** on the final line (`hit.unwrap().name`).

`contains_key` is correct for both hit and miss. `.get()` on the miss is
correctly nil. `.get()` on the hit returns a non-nil Option — but its payload
is corrupt: unwrapping it and reading `.name` crashes. `d["Read"]` (index
read), by contrast, returns a perfectly usable `Tr` (`idx name=Read n=5`).

### Probe C — safe alternative (all PASS)

```simple
val v = h.traits["Read"]        # index read
val o: Tr? = Some(v)            # manual Option wrap
```

- `o == nil` → `false`
- `o.unwrap().name` → `"Read"`
- passing `o` to a `Tr?` param → `"Read"`
- passing `v` to a plain `Tr` param → `"Read"`
- a `nil` `Tr?` through the same param → `"nil"`

So `Some(index_read)` round-trips correctly through every path tested; only
the runtime `.get()` decode is broken.

## Per-operation truth table (native codegen, `Dict<text, i64>` / `Dict<text, Tr>`)

| Operation                         | i64 value  | struct value | Notes |
|------------------------------------|:----------:|:------------:|-------|
| `.len()`                           | **broken** (-1) | **broken** (-1) | separate bug, see below |
| `.get(k)` — HIT                    | **broken** (undecoded, `raw` not `raw>>3`) | **broken** (non-nil, corrupt payload, segfault on use) | this bug |
| `.get(k)` — MISS                   | correct (nil) | correct (nil) | |
| `.keys()`                          | correct    | (not probed, expected correct — see below) | |
| `.contains_key(k)`                 | correct    | correct       | |
| `d[k]` index read — HIT            | correct    | correct       | |
| `Some(d[k])` manual wrap           | (not probed) | correct     | round-trips through `Tr?`/`Tr` params |

## Root-cause pointers (not yet applied — analysis only, this doc is docs-only)

`.get()` and `d[k]` **must decode identically** — they hit the same runtime
call (`rt_dict_get`) — but the MIR lowering paths that follow the call have
diverged:

- `.get()` lowering: `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:1244-1262`
  (`receiver_is_dict and method == "get"`). Resolves the value type via a
  **single-layer** fallback — `self.local_mir_type_of(receiver_local)`,
  matching only `MirTypeKind.Dict(_, value_type)`; if that lookup is nil,
  `get_value_type` stays at the default `MirType.i64()`. It then calls
  `self.decode_runtime_value(get_local2, get_value_type)` (line 1261) and
  **returns immediately** — no further bookkeeping on the decoded local.

- `d[k]` index-read lowering: `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:971-1031`
  (`self.local_is_runtime_dict(base_local)` arm). Resolves the value type via
  a **two-layer** fallback — first the builder's tracked local type
  (`self.builder.locals` scan for `base_local`), then, if that failed, the
  HIR-level type annotation on the base expression
  (`base.has_type_ == true and base.type_ != nil`, matching `Dict(_,
  value_type)`) — strictly more resolution power than `.get()`'s single
  lookup. After calling the same `self.decode_runtime_value(get_local,
  dict_result_type)` (line 1004), it has an extra step (lines 1005-1029,
  labeled "Bug #189" in the source comment) that, **when the decoded value's
  type is a Struct**, registers `self.struct_value_syms[decoded.id] =
  struct_type_sym.name` — this is what lets a later `.name`/`.n` field access
  on the decoded value resolve the correct field index via
  `resolve_field_index`. **`.get()`'s lowering has no equivalent step.**

This explains Probe B directly: `decode_runtime_value`'s default arm
(`expr_dispatch.spl:570-572`) does a correct raw pass-through for a
struct-typed result (right bits, no decode needed) — but without the
`struct_value_syms` registration that only the index-read path performs, the
struct identity of the `.get()`-returned local is unknown to
`resolve_field_index`, so `.unwrap().name` reads the wrong field index (or an
out-of-bounds one) — a garbage field read / segfault.

For Probe A, the same `.get()` vs `d[k]` value-type-resolution gap is the lead
suspect: `.get()`'s single-layer `local_mir_type_of` lookup can fail to
recover the dict's declared `i64` value type for a receiver reached through a
struct field or an erased chain link (a documented native-codegen landmine:
"Chained methods on erased receivers" in `.claude/rules/language.md`), landing
`decode_runtime_value` in a branch other than the integer arm — matching the
observed undecoded `56` (`7<<3`) rather than `7`. This is not yet bisected to
a specific branch; a targeted probe that dumps `get_value_type`'s resolved
`MirTypeKind` at the `.get()` call site would confirm it.

**`.len()` returning -1 is a SEPARATE bug**, not caused by this decode path —
see `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md`.

## Stage-4 impact (why this was misdiagnosed before)

This is the true root cause of the stage-4 bootstrap segfault previously
attributed to "header-only/partial modules with nil decl dicts"
(`doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`,
`doc/08_tracking/bug/native_nil_dict_get_phantom_option_rootcause_2026-07-27.md`).
Those docs correctly diagnose a *different* trigger (a **nil dict receiver**,
where the nil sentinel `3` gets shifted to a phantom `0` and reads as
non-nil). Probes A/B/C here show the corruption is broader: even a **valid,
non-nil dict with a real hit** produces a corrupt `.get()` result when the
value type is a struct — no nil receiver required.

`register_imported_symbol` in
`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` did:

```simple
val as_trait: Trait? = imported_mod.traits.get(name)
...
elif as_trait != nil:
    ...
    self.lower_trait(as_trait.unwrap())
```

`imported_mod.traits` is `Dict<text, Trait>` — a struct-valued dict, exactly
Probe B's shape. A **hit** on `std.io.traits`' `Read` entry (a real,
populated dict, not a nil stub) produced the corrupt Option described above,
and `as_trait.unwrap()` segfaulted at HIR module 32. The fix landing now:
every struct-valued dict lookup in `module_lowering.spl` is rewritten from
`.get(name)` + `.unwrap()` to `contains_key(name)` + index read `d[name]`,
which Probe C proves is safe.

## Suggested fix

Make `.get()`'s lowering (`method_calls_literals.spl:1244-1262`) decode
**identically** to `d[k]`'s (`expr_dispatch.spl:971-1031`):

1. Use the same two-layer value-type resolution (tracked builder-local type,
   then HIR-level `base.type_` fallback) instead of the single
   `local_mir_type_of` lookup, fixing Probe A's undecoded-integer symptom.
2. After `decode_runtime_value`, apply the same struct-symbol registration
   (`self.struct_value_syms[decoded.id] = struct_type_sym.name` when the
   result type is `MirTypeKind.Struct(...)`) that the index-read path already
   has (the "Bug #189" block, `expr_dispatch.spl:1005-1029`), fixing Probe
   B's corrupt-payload symptom.

The cleanest implementation is likely to factor the index-read arm's
value-type resolution + post-decode struct registration into a shared helper
that both `.get()` and `d[k]` call, so the two paths cannot re-diverge.

Until the runtime fix lands, callers should use the `contains_key` + index
read pattern (Probe C) instead of `.get()` on struct-valued dicts.

## Related

- `doc/08_tracking/bug/hir_stub_module_nil_dict_get_phantom_some_2026-07-27.md`
  — the nil-receiver phantom-Some family; same decode machinery, different
  (narrower) trigger.
- `doc/08_tracking/bug/native_nil_dict_get_phantom_option_rootcause_2026-07-27.md`
  — root-causes the nil-sentinel-shift mechanism in `decode_runtime_value`'s
  integer arm; complementary to this doc's struct-arm/value-type-resolution
  findings.
- `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md` —
  `.len()` returning -1, a separate bug on the same receivers.
- `test/01_unit/compiler/native/dict_get_struct_value_spec.spl` — regression
  spec pinning Probes B/C's contract.
- `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` —
  `register_imported_symbol`, the stage-4 crash site fixed by switching to
  `contains_key` + index read.

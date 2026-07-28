# Bug: `Dict.get()` on a MISS returns a zero VALUE, not `nil` (native codegen) — silent wrong branch

- **Date:** 2026-07-28
- **Status:** open
- **Area:** native codegen — MIR dict read lowering (`lower_dict_runtime_get` applies
  `decode_runtime_value` to `rt_dict_get`'s nil sentinel with no nil guard)
- **Severity:** **critical** — silent-wrong-answer. Nothing crashes; a missing key is
  indistinguishable from a present zero value. Higher severity than the
  `.get()`-struct-segfault class, which at least fails loudly.
- **Found by:** isolated native one-binary probes on a clean checkout of `origin/main`
  (`f1f75f0f81e`, which contains the `.get()` lowering fix `7e83e92ce314`)

## Summary

Under native codegen, `d.get(k)` for a **missing** key does not yield `nil`. It yields
the **zero value of the dict's value type**, decoded as if a real value had been found:

| `V` | `d.get(missing)` observed | `== nil` | `?? default` |
|---|---|---|---|
| `i64` | `0` | **false** | default **never applied** (yields `0`) |
| `bool` | `false` | **false** | — |
| `text` | non-nil | **false** | — |

Every `if d.get(k) == nil`, `d.get(k) ?? default`, and `val Some(x) = d.get(k) else:`
miss path therefore takes the **wrong branch**: a miss looks like a present zero.

Two related silent-wrong results fell out of the same probes:

- `d.get(k).?` is **not** a safe replacement: it reports **empty for a present value of
  `0`** (accidentally right on a miss, wrong on a stored zero).
- `Dict<text, bool>` — a **hit whose stored value is `true`** compares `== nil` as
  **true**, i.e. a present key reads as missing.

## This CHANGES a documented row

`doc/07_guide/language/dict_native_pitfalls.md` previously stated:

| `d.get(k)` — miss | correct, `nil` | yes |

That row is **wrong** and has been corrected. Several sweeps landed on 2026-07-27
reviewed call sites against the assumption that the miss path was safe; they need
revisiting.

## Not introduced by `7e83e92ce314`

This is **pre-existing**. The pre-fix `.get()` arm carried an explicit comment:

> "Missing-key behavior intentionally mirrors the existing `d[k]` raw-read path
> (pre-existing garbage-on-miss behavior documented in scratchpad/dict_native_report.md
> item 15 — not introduced here, not fixed here, out of scope for this sweep)."

and `scratchpad/dict_native_report.md` item 15 records:

> "Missing-key raw read `d["z"]` (no `.get`) | 3 (garbage) | 0 (garbage) | SILENT-WRONG
> both sides, pre-existing, unrelated to this fix — **flagging as a separate bug, not
> fixed here**"

That separate bug was never filed. This is that filing. `7e83e92ce314` did not cause
the defect, but by routing `.get()` through the index-read path it made `.get()`
inherit the index read's garbage-on-miss behaviour explicitly and permanently.

## Root cause (source-verified)

1. `rt_dict_get` on a miss returns `rt_core_nil()` = `RT_NIL` =
   `(SPECIAL_NIL << 3) | TAG_SPECIAL` = **3**
   (`src/runtime/runtime_native.c:4707-4716`, `src/runtime/runtime_value.h:13-20`).
2. `lower_dict_runtime_get` calls `decode_runtime_value` on that return value
   **unconditionally — there is no nil guard**
   (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:653-657`).
3. `decode_runtime_value` (`expr_dispatch.spl:493-583`) then unboxes the sentinel as if
   it were data:
   - integer arm (`:497-502`): `3 >> 3` → **0**
   - bool arm (`:503-507`): `3 == 11` → **false**
   - str arm (`:560-580`): `rt_interp_cstr(3)` → `!s && v < 0x10000` → **NULL**
   - default arm (`:581-583`): passthrough → `3` — the **only** arm that preserves nil
4. `x == nil` compares against the flat nil sentinel **3**
   (`switch_operators_calls.spl:1992`, `expr_dispatch.spl:2527`). `0 == 3` is false.

So exactly the value types whose decode arm transforms the raw word (integer, bool,
str) lose nil; struct/class/enum values survive because their arm passes the word
through untouched.

## Evidence

Built and run as standalone native ELF binaries (no interpreter involved — verified
`ELF 64-bit LSB pie executable`, and zero
`JIT compilation failed, falling back to interpreter` lines in any build log).

```
i64 CONTROL contains_hit=true contains_miss=false     <- control: contains_key correct
i64 HIT(7)  isnil=false val=7                          <- hit correct (7e83e92ce314 works)
i64 HIT(0)  isnil=false val=0
i64 MISS    isnil=false val=0                          <- *** MISS IS 0, NOT NIL ***
i64 MISS ??-77 = 0                                     <- *** ?? default never fires ***
bool HIT(true)  isnil=true  val=true                   <- *** present true reads as nil ***
bool HIT(false) isnil=false val=false
bool MISS       isnil=false val=false                  <- *** MISS IS false, NOT NIL ***
text HIT   isnil=false val=yes
text MISS  isnil=false                                 <- *** MISS NOT NIL ***
```

```
idx-read MISS val=0                                    <- item 15 reconfirmed
eq-nil MISS: NOT nil (WRONG)
opt-has MISS: empty (CORRECT)
bool HIT(true): reads NIL (WRONG)
```

```
get(zero=0).? -> EMPTY (WRONG: present 0 looks missing)
get(seven=7).? -> HAS value (CORRECT)
get(MISS).?    -> EMPTY (CORRECT)
zero ??-77 = 0   MISS ??-77 = 0
```

## Not measured

**Struct/class/enum value types could not be measured by native-build.** Any
module-level `struct` declaration makes native-build fail with
`error: AOT compile error: MIR module has no functions` (a separate native-build
defect), so `Dict<text, StructValue>` and dict-as-struct-field were not exercised at
runtime. Static reading of the default decode arm (step 3 above) says struct values
**do** preserve nil on a miss, but that is analysis, not measurement — treat it as
unverified.

## Reproduce

Requires a clean tree (the local working copy's uncommitted
`driver_source_loading.spl` edit breaks native-build with
`function source_file_coverage_identity not found`):

```bash
git worktree add --detach /tmp/dictwt <sha-containing-7e83e92ce314>
mkdir -p /tmp/dictwt/bin/release/x86_64-unknown-linux-gnu
cp bin/release/x86_64-unknown-linux-gnu/simple /tmp/dictwt/bin/release/x86_64-unknown-linux-gnu/
ln -sf release/x86_64-unknown-linux-gnu/simple /tmp/dictwt/bin/simple
cd /tmp/dictwt && ./bin/simple native-build min.spl -o min && ./min
```

```simple
fn main():
    var d: Dict<text, i64> = {}
    d["hit"] = 7
    val m = d.get("ZZZ")
    val mn = m == nil
    print "MISS isnil={mn}"      # prints false; must print true
```

## Suggested fix

Guard the decode in `lower_dict_runtime_get`: branch on the raw `rt_dict_get` result
being the nil sentinel **before** calling `decode_runtime_value`, and yield the nil
sentinel unchanged on that path. The same guard fixes `d[k]`, `.get()`, `??`, and
`== nil` together, since all four now share the one lowering.

Note that a correct fix must also make a present `0` / `false` distinguishable from a
miss — decoding alone cannot carry that bit, so `.get()` needs a real `Option`
representation (a `contains_key` probe, or an out-of-band found flag), not just a
sentinel passthrough.

## Related

- `doc/07_guide/language/dict_native_pitfalls.md` — truth table (MISS row corrected by this bug)
- `doc/08_tracking/bug/native_dict_get_struct_value_corrupt_option_2026-07-27.md` — the HIT-side defect, fixed by `7e83e92ce314`
- `doc/08_tracking/bug/native_dict_len_returns_minus_one_2026-07-27.md` — `.len()` always -1
- `scratchpad/dict_native_report.md` item 15 — the original unfiled sighting

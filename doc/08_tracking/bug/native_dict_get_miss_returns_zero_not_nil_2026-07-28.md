# Bug: `Dict.get()` on a MISS returns a zero VALUE, not `nil` (native codegen) — silent wrong branch

- **Date:** 2026-07-28
- **Status:** **FIXED for `i64`, `text`, `bool` and struct value types (2026-08-17).**
  `f64` remains out of scope (no room for a sentinel in a float word), as does
  `d[k]`-on-a-miss (an index read is not an Option and has nowhere to put a
  miss signal).

## 2026-08-17 — the "residual text gap" was not a text gap: the fix was UN-WIRED

The 2026-08-01 entry below is accurate about what it built and wrong about what
shipped. Re-measured today on a native `--entry-closure` build, **every** value
type reproduced the ORIGINAL pre-fix behaviour, including the two this doc
recorded as FIXED:

| probe | measured 2026-08-17 (before) | after |
|---|---|---|
| `Dict<text,i64>` miss `== nil` | `NOTNIL` | **`NIL`** |
| `Dict<text,i64>` miss `?? -77` | `0` | **`-77`** |
| `Dict<text,text>` miss `== nil` | `NOTNIL` | **`NIL`** |

Root cause, from the emitted LLVM IR: **no guard blocks were emitted at all** —
no `dict_get_miss_nil` / `dict_get_hit_value` / `dict_get_merge` appeared
anywhere, and `rt_interp_cstr(i64 3)` was applied to the sentinel
unconditionally. `dict_get_preserve_flat_nil` was never reached because
`lower_dict_runtime_read`'s `as_option` parameter was **never true at any call
site in the tree**: `.get(k)`'s arm
(`_MirLoweringExpr/method_calls_literals.spl`) called `lower_dict_runtime_get`,
a one-line wrapper that hardcodes `as_option: false`. The entire guard — and
the `Option<bool>` raw-word arm with it — was dead code.

So this was never a str-specific decode problem. The earlier note that "the str
guard is emitted but does not change the observed result" was a mis-diagnosis:
the guard was not emitted. The 2026-08-01 work was correct and simply
disconnected, most likely when the `.get` arm was re-routed through the shared
helper to fix the struct-value corruption
(`native_dict_get_struct_value_corrupt_option_2026-07-27`) — that change made
both readers identical, which is right for resolve/decode/register and wrong
for the one axis on which they must differ.

**Fix:** call `lower_dict_runtime_read(..., true)` directly from the `.get(k)`
arm. `d[k]` still goes through `lower_dict_runtime_get` unchanged.

**Why nothing caught the regression:** `dict_get_miss_returns_nil_spec.spl`
drives only the `interpret` and `jit` engines out of process, and its own header
states its in-process examples are green before and after the MIR fix. The
defect lives in lowering that only the native lane compiles, so no spec
exercised the lane that could fail. Closed by
`test/01_unit/compiler/codegen/native_dict_get_miss_sentinel_class_spec.spl`,
which builds natively and asserts both halves of the contract — a miss reads
nil AND a stored `0` / empty string / `false` does not.

- **Status (historical, superseded):** FIXED for `i64` and `bool` value types (2026-08-01); **still open for `text`**
- **Area:** native codegen — MIR dict read lowering (`lower_dict_runtime_get` applies
  `decode_runtime_value` to `rt_dict_get`'s nil sentinel with no nil guard)
- **Severity:** **critical** — silent-wrong-answer. Nothing crashes; a missing key is
  indistinguishable from a present zero value. Higher severity than the
  `.get()`-struct-segfault class, which at least fails loudly.
- **Found by:** isolated native one-binary probes on a clean checkout of `origin/main`
  (`f1f75f0f81e`, which contains the `.get()` lowering fix `7e83e92ce314`)

## Fix (2026-08-01) — integer and bool value types

`lower_dict_runtime_get` was split into `lower_dict_runtime_read(..., as_option)`
so the two readers of `rt_dict_get` can differ where they must:

- `d[k]` (`as_option: false`) is byte-for-byte unchanged — an index read has
  no `Option` to return, so there is nowhere for a miss signal to go.
- `d.get(k)` (`as_option: true`) declares `V?`, so the MISS sentinel is now
  routed **around** the decode by `dict_get_preserve_flat_nil`
  (`select(raw == 3, 3, decode(raw))`, built with the same block/merge shape
  the `Option.map` lowering already uses). Guarded to the value types whose
  decode arm actually transforms the raw word — integer and str — via the new
  shared `mir_type_is_integer` predicate, which `decode_runtime_value` now
  also uses so the two can never disagree.
- `Dict<_, bool>.get(k)` returns the **raw word undecoded**: an `Option<bool>`
  has three states (`11` / `0` / `3`) and an `i1` holds two, and
  `option_bool_value` is already the matching decode. That fixes the miss AND
  the "a present `true` compares equal to `nil`" row in the same change.

### Measured, native ELF, `Dict<text,i64>` / `Dict<text,bool>` / `Dict<text,text>`

| probe | before | after | verdict |
|---|---|---|---|
| `i64` miss `== nil` | `false` | **`true`** | fixed |
| `i64` miss `?? -77` | `0` | **`-77`** | fixed |
| `i64` stored-zero `== nil` | `false` | `false` | unchanged, correct |
| `bool` miss `== nil` | (was `false`) | **`true`** | fixed |
| `bool` present-`true` `== nil` | (was `true`) | **`false`** | fixed |
| **`text` miss `== nil`** | `false` | **`false`** | **STILL BROKEN** |
| `text` hit `== nil` | `false` | `false` | unchanged, correct |
| `.len()` local / param | `2` / `2` | `2` / `2` | unchanged, correct |

**Residual — `text` value types.** The str guard is emitted but does not
change the observed result; the sentinel is either not surviving
`emit_cast(3, Opaque("str"))` or `== nil` on a str-typed local does not
compare against the flat sentinel. Not diagnosed. `Dict<text, text>.get()`
on a miss is still indistinguishable from a hit — keep using
`contains_key(k)` + `d[k]` for text-valued dicts.

**Also not fixed:** `f64` value types (the flat ABI has no room for a
sentinel in a float word, same shape as the `bool` case but with no
alternative encoding), and `d[k]`-on-a-miss, which is out of scope by
design as described above.

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

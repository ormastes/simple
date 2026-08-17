# native-build: text value stored into an empty-`{}` dict SIGSEGVs on read/compare

- **id:** native_empty_dict_text_value_sigsegv_2026-07-20
- **status:** open
- **severity:** high (crash — any string value through an empty-literal dict on native)
- **found:** 2026-07-20, during f64 empty-container hardening verification
- **paths affected:** native-build only (`run`/interp returns rc 30 correctly)

## Repro

```simple
fn main() -> i64:
    var d = {}
    d["k"] = "hi"
    if d["k"] == "hi":
        return 30
    return 40
```

`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry repro.spl -o repro --clean`
→ binary SIGSEGVs (rc 139). Reproducible across independent `--clean` builds
(fault addresses `0xb8c5b1456c2` / `0xac792bb74c2` / `0xb08dd3d40c2`, same
return-address offsets `+0x25f4`/`+0x3366`/`+0x24bc` relative to binary base —
same fault site every time).

## Pre-existing — NOT caused by the f64 empty-container fix

Verified to SIGSEGV identically on a **pristine clean-origin-tip worktree**
(`2422a556b90`, no local edits) with the same command. The
`runtime_elem_value_type` hardening (same session) only records F64/F32 store
types and only rewrites reads whose static element type is the erased i64
default — a text store never enters that map.

Contrast (all rc 30 on native at the same tip + hardening):
- `val d = {"k": "hi"}` … dict **literal** with text value — works.
- `var d = {}; d["k"] = 0.1` / `= 7` — f64/int through the same empty-dict
  store path — work.

So the defect is specific to the TEXT-value store or the read/compare of a
text value whose dict local carries the erased i64 default element type: the
read side treats the tagged string handle as an i64 (`>>3` decode / raw
compare), then dereferences the shredded pointer in the string-equality path.
Likely fix direction: extend the store-observed-type refinement
(`runtime_elem_value_type`) or `bin_is_str_eq` detection to cover text stores
into erased-element-type containers; root-cause properly before patching.

## Notes

- Discovered by probe 9 of the hardening verification sweep; probes for f64,
  i64, and mixed f64/int through the identical path all pass rc 30.
- See `seed_f64_array_element_precision_mask_2026-07-19.md` (hardening-sweep
  banner) for the sibling f64 fix this was found alongside.

## REPRODUCED 2026-08-17 — but the filed symptom is WRONG, and the real one is worse

The native build completed (`BUILD_RC=0`, ~50 min for a 7-line program). **It does
not SIGSEGV.** It returns a silently wrong value — which puts this row in the
silently-wrong-results class, where a crash-titled doc will never be recognised.

| arm | `got=` | `eq=` | `len=` |
|---|---|---|---|
| `interpret` | `hello` | true | 1 |
| `jit` | `hello` | true | 1 |
| **native-build** | **`109691254279185`** | **true** | **1** |

The wrong value decodes cleanly: `109691254279185` = `0x63C37C3F0C11`, a Linux
heap address whose low 3 bits are `001` — a **correctly tagged**
`RT_VALUE_TAG_HEAP` text pointer. With `eq=true` and `len=1`, that proves the dict
**stored and retrieved the text correctly**. Nothing is null and nothing is
corrupt, so the doc's "null struct deref / SIGSEGV on read or compare" root cause
is not what happens.

What breaks is `"got=" + v`: the native `+` lowering rendered a tagged pointer as
a **decimal integer** instead of concatenating it as text. That is a static-type
decision, not a runtime one — `expr_dispatch.spl bin_is_str_concat` chooses
between `rt_strcat_tagged` and integer add, and `runtime_native.c:5847-5862`
documents that contract. A dict read yields `any`, so the static test appears to
fall through to the integer arm.

**Not yet asserted.** A four-arm discriminating build was still running: plain
text (positive control), non-empty dict literal, empty dict literal, plus
`eq`/`len`. If plain text ALSO renders as a pointer, the dict is entirely
innocent and this row is misfiled against the wrong subsystem; if only the dict
arms break, it is dict-read type-loss as described.

**Scope:** if that holds, the root cause is in `src/compiler/70.backend/**`, not
`src/os` or `src/runtime` — diagnosis and hand-off, not a patch from this lane.

**Recommended retitle** once the discriminator lands: this is a native-only
wrong-value defect on text concatenation of an `any`-typed value, not a dict
SIGSEGV.

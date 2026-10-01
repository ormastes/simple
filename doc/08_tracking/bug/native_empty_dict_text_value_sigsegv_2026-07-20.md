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

## Attempted re-measurement 2026-09-18 — NOT reproduced, and not refuted either

This entry could not be re-measured on Linux aarch64 today, and the reason is
worth recording so the next attempt does not spend the same hour.

The repro command above (`native-build --entry repro.spl`) never reaches
codegen on this host. Working through it in order:

1. `native-build` first refused with `SCV-E-ADMISSION:
   compile-event-journal-missing`, whose named remedy
   (`SIMPLE_SCV_INVENTORY_COLD_INIT=1`) then published an EMPTY inventory and
   wedged the cache permanently — a separate defect found while chasing this
   one, fixed fail-closed in PR #1084 and recorded in
   `seed_jit_optional_unwrap_returns_enum_box_2026-09-18.md`.
2. With a sound binary and a clean cache the inventory builds correctly
   (16,797 entries), and the build then stops at `SCV-E-SNAPSHOT:
   snapshot-inventory-empty`, cleared by the documented opt-in
   `SIMPLE_SCV_FREEZE_FALLBACK=1` (these fixtures live outside the `src` root
   the freeze covers).
3. Past that it stops at `error: persistent package index admission failed:
   scv-authority-missing`, and `SIMPLE_PACKAGE_INDEX_COLD_INIT=1` then leads to
   `filesystem-event-journal-missing`. That is where it ends: **no native
   artifact is produced, so there is nothing to run and nothing to observe.**

So the interpret and JIT lanes return rc 30 as this entry already says, and the
native lane — the only one where this bug lives — cannot be exercised here at
all. Treat this entry as UNVERIFIED-since-2026-07-20 rather than as reproduced
or fixed; a native row measured under any of the workarounds above would be
manufactured, not observed.

The same blocker is why `check-engine-differential`'s native lane answers 0 of
19 fixtures (see that gate's DEGRADED COVERAGE line). Whoever clears the
persistent package index unblocks both at once, and this entry becomes
measurable again.

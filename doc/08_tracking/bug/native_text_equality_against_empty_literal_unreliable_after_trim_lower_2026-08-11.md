# Native codegen: `x != ""` unreliable for text built via `.trim().lower()` chains

## Status
OPEN — NEW DEFECT (compiler/codegen family). Discovered and worked around
at one call site 2026-08-11; not yet swept tree-wide. Tag: text
`(ptr,len)` ABI family (see `.claude/memory` reference entries
`reference_pure_simple_codegen_lacks_text_ptr_len_abi.md`,
`reference_native_tuple_to_text_prints_raw_pointer.md`,
`reference_native_slice_splits_utf8_no_validation.md` — this is a new
member of that family: text **equality-against-empty-literal**, not a
decode/print issue).

## Symptom (measured live, x86_64 OVMF real-firmware boot, native/AOT
freestanding baremetal build — see companion doc
`doc/08_tracking/bug/simpleos_baremetal_backend_resolve_empty_override_rt_process_run_trap_2026-08-11.md`
for the full incident)

Location: `src/lib/gc_async_mut/gpu/engine2d/engine.spl`,
`detect_best_backend_viable()`, around line 1035 (pre-fix):

```
val override_name = engine2d_env_backend_override()   # via .trim()
if override_name != "":                                 # TRUE (should be FALSE)
    val override_canon = backend_canonical_name(override_name)  # via .trim().lower()
    val override_probe = Engine2D.probe_backend(1, 1, override_canon)
    ...
    print("[backend-resolve] override {override_canon} rejected: {override_probe.reason}")
```

Live serial output:
```
[backend-resolve] override  rejected: Unknown backend: 
```
Note the **literal double space** between `override` and `rejected` — the
`{override_canon}` interpolation rendered as empty text. Yet the `if
override_canon != "":`-shaped guard (both here and in the immediate
ancestor `if override_name != "":`) evaluated **TRUE**, entering a branch
that should only be reachable for a genuinely non-empty backend name. This
routed an effectively-empty value into `Engine2D.probe_backend(1, 1, "")`,
which always fails (`"Unknown backend: "`, `engine.spl:861`), and
completely bypassed the real auto-resolution priority order.

So: the value **prints/interpolates as empty**, but **does not compare
equal to the `""` literal**. Both cannot be true for a correctly-represented
text value — this is a native-codegen bug in text equality comparison (or in
how `.trim()`/`.lower()` construct the returned text object), not a logic
error in the calling code.

## Root cause hypothesis (not yet proven at the codegen/IR level)

`override_name` and `override_canon` are both produced through chains of
`.trim()` / `.lower()` string transforms (see
`engine2d_env_backend_override()` — `raw.trim()` — and
`backend_canonical_name()` — `name.trim().lower()`, both in
`src/lib/gc_async_mut/gpu/engine2d/engine.spl` /
`src/lib/gc_async_mut/gpu/engine2d/helpers_availability.spl`). The
`(pointer, length)` text representation these ops return appears to have a
length field that's inconsistent with the actual (empty) content —
consistent with the broader "pure-Simple codegen lacks a correct (ptr,len)
text ABI" defect family already tracked, but this is the first observed
instance where it corrupts an **equality comparison** outcome rather than a
`to_text()`/print/interpolation outcome. Not confirmed via disassembly
within this pass — filed as a hypothesis for follow-up codegen-level
investigation (MIR/LLVM lowering of text `==` against a literal).

## Workaround applied (proven effective)

Replace `x != ""` / `x == ""` guards on text values built via such chains
with a **length check** instead of text-literal equality:

```
if override_name.len() > 0:
    val override_canon = backend_canonical_name(override_name)
    if override_canon.len() > 0:
        ...
```

Verified live: after switching to `.len()`, the bogus
`"[backend-resolve] override  rejected: Unknown backend: "` line no longer
appears in serial output across a rebuilt kernel (confirmed via
`grep -a -c "override ignored"` returning 1 hit against the freshly-linked
ELF, i.e. the new code path is compiled in and taking the length-based
branch correctly).

## Scope / impact — NOT YET SWEPT

This was found and fixed at exactly one call site under time pressure while
chasing an unrelated SimpleOS boot defect. **This pattern (`!= ""` /
`== ""` against a `.trim()`/`.lower()`-derived text value, under native/AOT
codegen, especially on baremetal/freestanding targets) may be silently wrong
at other call sites tree-wide.** A full sweep was explicitly out of scope
for this pass (do not attempt further tracing this session — see chained
decision in this file's companion bug doc). Recommended follow-up:

1. `grep -rn '!= ""' src/lib src/os src/compiler | grep -i 'trim\|lower\|canonical'`
   to enumerate candidate call sites where a trimmed/lowered value feeds a
   `!= ""` guard.
2. A minimal reproduction: a small native-target (or `--native`) test that
   does `val x = " FOO ".trim().lower(); assert x.len() == 3; assert x !=
   ""` and prints the interpolated value, to isolate whether the bug is
   general to native/AOT or specific to the freestanding baremetal
   backend used by this build (`--target x86_64-unknown-none`,
   `SIMPLE_ALLOW_FREESTANDING_STUBS=1`, `--backend llvm` via
   `native-build --entry-closure`).
3. If reproducible outside SimpleOS, escalate as a general compiler defect
   (not baremetal-specific) and cross-link from
   `doc/07_guide/language/dict_native_pitfalls.md`-style native-codegen
   pitfall docs.

## Related known defects (same general ABI family, different symptom)
- `reference_pure_simple_codegen_lacks_text_ptr_len_abi.md`
- `reference_native_tuple_to_text_prints_raw_pointer.md`
- `reference_native_slice_splits_utf8_no_validation.md`
- `reference_to_text_on_erased_any_bool_corrupt.md`

## Evidence
Full before/after serial tails and gate verdicts:
`doc/08_tracking/bug/simpleos_baremetal_backend_resolve_empty_override_rt_process_run_trap_2026-08-11.md`

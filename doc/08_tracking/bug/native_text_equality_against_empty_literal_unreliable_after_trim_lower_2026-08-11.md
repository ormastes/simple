# Native codegen: `x != ""` unreliable for text built via `.trim().lower()` chains

## Status
**RESOLVED 2026-08-11** — root-caused and fixed in the runtime across all six
freestanding lanes. See "## Root cause (PROVEN)" and "## Fix" below, which
supersede the hypothesis and the "NOT YET SWEPT" section further down (both
retained for history). The `(ptr,len)` ABI hypothesis was **wrong**; the actual
cause is a missing heap-vs-raw arm in the freestanding `rt_native_eq`.
Scope correction: the defect is **freestanding/baremetal-only** — hosted
native (`compile --native`) was measured CLEAN and matches the interpreter.

Original status line: OPEN — NEW DEFECT (compiler/codegen family). Discovered
and worked around at one call site 2026-08-11; not yet swept tree-wide. Tag: text
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

## Root cause (PROVEN, 2026-08-11)

**Not a `(ptr,len)` ABI defect, and not in codegen at all — a missing case in
the freestanding runtime's equality primitive.**

`examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c:1472`
(`rt_native_eq`, which `!=` reaches via `rt_native_neq` at :1493):

```c
RuntimeValue rt_native_eq(RuntimeValue a, RuntimeValue b)
{
    if (a == b) return 1;
    if (IS_HEAP(a) && IS_HEAP(b)) {     /* <-- content compare ONLY here */
        ... compare sa->data vs sb->data ...
    }
    return 0;                            /* <-- everything else: NOT EQUAL */
}
```

The two operands have **different representations**:

| operand | representation | `IS_HEAP`? |
|---|---|---|
| `.trim()` / `.lower()` result | heap `RuntimeString` (always freshly malloc'd by `rt_string_slice` / `rt_string_to_lower`) | yes |
| bare `""` literal | RAW untagged `char*` global (`emit_bootstrap_str_const`) | **no** |

So the mixed pair skipped the content compare and fell straight to
`return 0` — **"not equal", unconditionally, regardless of content**. Hence
`x != ""` was TRUE for a genuinely empty `x`.

This also explains the two facts that made the symptom look impossible:
- `{x}` interpolates as empty — interpolation decodes the heap string
  honestly and prints its true (zero-length) content. No literal involved.
- `.len() == 0` works — `.len()` reads the heap header's `len` field
  directly. No literal involved.

Both "contradictory" observations are consistent: only the *comparison against
a literal* was broken.

**Why it exists:** this is hosted bug **#148**, which was fixed on the hosted
lane by introducing `rt_text_eq_any` (tagged-or-raw normalization,
`src/runtime/runtime_native.c:3361`) — and **never ported to the freestanding
lanes, which have no `rt_text_eq_any` at all**. Those lanes *did* receive the
ORDERING counterpart `rt_text_cmp_any` (`baremetal_stubs.c:14566`), which is
what made the gap easy to miss: text ordering was fixed, text equality was not.

**Hosted native is NOT affected** (measured, see "## Red-then-green"): on the
hosted lane MIR lowering routes text `==`/`!=` to `rt_text_eq_any`, which
normalizes both operands via `rt_interp_cstr` and compares content.

## Fix

Give the freestanding lanes the heap-vs-raw arm their hosted counterpart has.
Six files, two shapes (both keep the pre-existing heap/heap and identity paths
byte-for-byte unchanged):

- `rt_native_eq_mixed_text()` + `rt_text_eq_heap_vs_raw()` —
  `examples/09_embedded/simple_os/arch/{x86_64,arm64,arm32,x86_32}/boot/baremetal_stubs.c`
- `rt_text_eq_str_vs_raw()` —
  `examples/09_embedded/simple_os/arch/aarch64/boot/freestanding_runtime.c`,
  `src/os/kernel/arch/riscv64/boot/freestanding_runtime.c`

Fixed at the primitive, so **no call site needs rewriting** — the ~7,400
existing `== ""` / `!= ""` sites become correct on these lanes automatically.

Deliberately conservative, because `TAG_INT` is `0x0` on these lanes so a raw
pointer is indistinguishable from a tagged small integer by tag bits alone —
the ambiguity behind
`native_text_eq_any_untagged_smallint_deref_2026-07-23.md`. Two guards:
the raw path is entered **only when the other operand is a proven heap
string** (so a word is reinterpreted as `char*` only inside a known-text
comparison), and a `< 0x10000` plausibility floor rejects nil/bools/small ints.
The scan is bounded by the heap string's own `len` and requires a NUL exactly
at that offset, so it never reads past the literal.

## Red-then-green (verbatim)

Hosted native lane — **does not reproduce**; native matches the interpreter
oracle exactly on direct chains and across function boundaries
(`.trim()`, `.lower()`, `.trim().lower()` on parameters and returns), so the
defect is freestanding-only:

```
=== cross-function chain truth table ===        (identical interp and --native)
fn-ret-trim(empty)         | eq="":1 | ne="":0 | len:0 | interp:[]
param-trim-lower(empty)    | eq="":1 | ne="":0 | len:0 | interp:[]
param-trim-lower(nonempty) | eq="":0 | ne="":1 | len:6 | interp:[vulkan]
param-trim-lower(spaces)   | eq="":1 | ne="":0 | len:0 | interp:[]
```

Freestanding predicate, via
`src/runtime/test/rt_native_eq_heap_vs_raw_empty_literal_selfcheck.c`
(replicates the lane's exact encoding; refuses to pass vacuously — exits 2 if
the defect fails to reproduce with the old predicate):

```
== BEFORE (shipped freestanding rt_native_eq) ==
  REPRODUCED: heap "" == raw "" -> NOT EQUAL (so `x != ""` is TRUE)
== AFTER (heap-vs-raw content comparison) ==
  ok   heap ""     == raw ""      (empty trim/lower result) = 1
  ok   raw  ""     == heap ""     (operands swapped)        = 1
  ok   heap "vulkan" == raw "vulkan"                        = 1
  ok   heap "vulkan" == raw ""          (must be NOT equal) = 0
  ok   heap ""       == raw "vulkan"    (must be NOT equal) = 0
  ok   heap "metal"  == raw "vulkan"    (must be NOT equal) = 0
  ok   heap "vulkan" == heap "vulkan"                       = 1
  ok   heap "vulkan" == heap "metal"   (must be NOT equal)  = 0
  ok   heap ""       == heap ""                             = 1
  ok   heap ""       == nil            (must be NOT equal)  = 0
  ok   heap "vulkan" == small int 7    (must be NOT equal)  = 0
  ok   heap ""       == small int 0    (must be NOT equal)  = 0

PASS - 12 assertion(s) checked, defect reproduced before / fixed after
```

Negative controls included above: non-empty text still compares correctly
(`"a" != ""` stays TRUE), the heap/heap path is unchanged, and small
non-pointer words are never dereferenced.

## Guard

`scripts/check/check-freestanding-text-eq-raw-literal.shs` — verdict as the
last stdout line (`PASS — <n> check(s) ...` / `FAIL` 1 / `ERROR — nothing was
checked` 2). It runs the selfcheck, asserts all six lanes carry the fix, and
FAILs on any **unlisted** freestanding `rt_native_eq` so a newly added lane
cannot silently ship without it. Proven fail-closed: removing the fix from one
lane yields `FAIL — 1 of 8 check(s) failed` exit 1; restoring yields exit 0.

## Blast radius (measured, no rewrites needed)

`== ""` / `!= ""` occurrences (anchored, owned code only):

| tree | `!= ""` | `== ""` |
|---|---|---|
| `src/lib` | 2,579 | 2,860 |
| `src/compiler` | 1,162 | 814 |
| **total** | **3,741** | **3,674** |

7,415 sites, all of which were exposed on the freestanding lanes and are fixed
by the runtime change. **Deliberately NOT rewritten** — the `.len()`-based
workaround applied to `engine.spl` is no longer required, though it is left in
place as it is equally correct.

## Root cause hypothesis (SUPERSEDED — original text, kept for history)

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

## Scope / impact — SUPERSEDED (swept; original text kept for history)

> Resolved by the runtime fix above. Answering this section's own follow-ups:
> (1) no call-site enumeration is needed — the fix is at the primitive;
> (2) the minimal reproduction was built and is **clean on hosted `--native`**,
> so the defect is **specific to the freestanding baremetal backend**, exactly
> the alternative this section flagged; (3) it is therefore NOT a general
> compiler defect and needs no cross-link from the native-pitfall docs.

### Original text

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

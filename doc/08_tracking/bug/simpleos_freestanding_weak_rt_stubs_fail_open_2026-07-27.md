# SimpleOS freestanding link fails open: ~4,022 weak `rt_*` stubs return NIL, silently zeroing real data

- **ID:** simpleos_freestanding_weak_rt_stubs_fail_open_2026-07-27
- **Date:** 2026-07-27
- **Area:** SimpleOS freestanding x86_64 link path —
  `examples/09_embedded/simple_os/arch/x86_64/boot/auto_stubs.c`; the
  pure-Simple SimpleOS linker (no fake-stub guard)
- **Severity:** high — silent data corruption in the guest, no crash, no
  diagnostic. Broke the SimpleOS-WM x QEMU showcase cell with
  `guest-render-fault`.
- **Status:** **FIXED AND LANDED** — `d1f87b4a1a7` (11 runtime functions) +
  `603e586ad5b` (nil-deref follow-up). **The systemic gap remains OPEN:** the
  pure-Simple SimpleOS link path still has no fake-stub guard, so the next
  missing symbol will fail open exactly the same way.
- **Supersedes:** the earlier symptom-named write-up of this same
  investigation (`llvmlib_freestanding_aggregate_return_empty_...`), whose
  proposed compiler mechanisms are **retracted** — see "Retracted mechanisms".

## Root cause

`examples/09_embedded/simple_os/arch/x86_64/boot/auto_stubs.c` defines **4,022
`__attribute__((weak))` `rt_*` stubs** that return `NIL_VALUE`. Any `rt_*`
symbol with no freestanding implementation **silently binds to one**. The link
succeeds, nothing warns, and the function returns 0 forever.

This is a **fail-open link**, not a compiler defect.

### Proof — direct inspection of the guest kernel ELF

```
nm:      088561a0 W rt_array_copy          <- W = weak
objdump: push %rbp; mov %rsp,%rbp; xor %eax,%eax; pop %rbp; ret   <- returns 0 unconditionally
```

### Why that one symbol zeroed the CSS engine

MIR lowers **every** `var x = <array-typed place read>` (the array-place-alias
copy, `var c = arr`) through `rt_array_copy`
(`src/compiler/50.mir/mir_lowering_stmts.spl:240-254`; the lowering is named
explicitly in the runtime's own comment at
`src/runtime/runtime_native.c:3895-3908`).

In the guest, therefore, **every array copy produced 0** — an un-tagged word.
The compiler's inline element reader tests `tag == 1` and otherwise leaves the
default `$0x3` nil, so `.len()` on the copy read **0**. Silently.

**Hosted builds were never affected:** `src/runtime/runtime_native.c:3908`
defines the real `rt_array_copy`. Its own comment documents *this same
corruption class from an earlier incident* — an array-place-alias copy that
zeroed `files.len()`. The failure mode had already been seen once and paid for.

## Fix and confirmation

Implementing `rt_array_copy` in `baremetal_stubs.c` moved the guest receipts:

| receipt | before | after |
|---|---|---|
| selector buckets | `class_keys=0 tag_keys=0 fallback=0` | `class_keys=34 tag_keys=4 fallback=3` |
| contract node CSS rules matched | 0 of 26 | 8 |
| `content-provenance-rejected` | 3 windows | **0** |

A second symbol of the same class was then found and fixed the same way:
**`rt_byte_array_new_len`**.

### Landed fix — `d1f87b4a1a7`

Implemented **11 missing freestanding runtime functions**:

`rt_array_copy`, `rt_byte_array_new_len`, `rt_enum_id`, `rt_text_cmp_any`,
`rt_text_count_codepoints_cached`, `rt_text_validate_utf8`,
`rt_string_to_float`, `rt_u32s_from_raw`, `rt_write_u32s_to_raw`,
`rt_ptr_write_u8`, `rt_time_now_monotonic_ms`.

### Follow-up — `603e586ad5b`, a nil-deref introduced by the fix itself

`d1f87b4a1a7` introduced a crash: `runtime_array_from_abi` casts a **non-heap
word straight to a pointer and dereferences it**, so `rt_array_copy(nil)`
segfaulted (loading from address 3).

**Lesson worth keeping: the guard written for exactly that case was
unreachable.** The defence existed in the source and never ran. It was caught
by **differential testing, not by the lane** — the guest lane would have
reported a fault far downstream, if at all.

### Verification technique — differential testing against hosted implementations

The C functions were **extracted into a host harness and compared against the
hosted/reference implementations across edge cases: 740 assertions.** This
confirmed the other 9 correct, including **0-ULP agreement with `strtod` across
denormals**.

Adopt this shape generally: a freestanding runtime function has a hosted twin,
and the twin is executable ground truth. Comparing them on a host is orders of
magnitude cheaper and more sensitive than exercising them through a guest.

### Three more fail-open stubs — and a prefix-allowlist NEAR MISS

Three further fabricated stubs were then found, and they matter enormously —
they are **the actual framebuffer span blitters**:

- `rt_engine2d_simd_blend_row_u32`
- `rt_engine2d_simd_copy_span_u32`
- `rt_engine2d_simd_fill_span_u32`

**They were nearly missed because a PREFIX allowlist (`rt_simd_`) would have
swallowed them.** These are `rt_engine2d_simd_*`, not `rt_simd_*`, and a
prefix rule written for "SIMD accelerators are optional, let them no-op" would
have silently exempted the functions that actually paint every pixel.

**Rule: classify these symbols by what the symbol DOES, never by prefix.** A
name-shaped allowlist is itself a fail-open mechanism — the same class of
mistake as the weak stubs it is meant to govern. Any allowlist in the guard
below must enumerate symbols explicitly, with a stated reason per entry.

## Why flat `[text]` survived while nested shapes did not

This is the useful lesson, and the earlier framing got it backwards.

**It is about which code paths perform an array COPY — not about nesting
depth.** Nested shapes are not intrinsically fragile. They simply route through
the array-place-alias copy (`var x = <array-typed place read>`) far more often,
and that lowering was the one bound to the zero-returning stub. A flat `[text]`
that never crosses a copy path survives untouched; a flat array that does cross
one would have died identically.

Any "deep vs flat", "nesting depth", or "aggregate return boundary" reading of
the receipts is an artifact of which sites happened to copy. Diagnose by asking
*does this path call a `rt_*` symbol that might be fabricated?*, not *how deeply
nested is this type?*

## Retracted mechanisms

Both mechanisms previously proposed in this investigation are **WRONG as
stated**, and are retracted. They were plausible from source reading and are
**disproven by experiment**:

- ~~**Defect A** — "nested-array element reads shredded in `lower_index_expr`"
  (wrong element type → `raw >> 3` / `rt_interp_cstr` on an inner handle).~~
- ~~**Defect B** — "call result used as a struct-constructor field argument
  loses its declared return type under `SIMPLE_BOOTSTRAP=1`".~~

**How they were disproven:** two compiler patches implementing them produced
**byte-identical object code** for the failing module — proving the patched
code never reaches that path at all. One of them additionally introduced an
`Engine2D.clear` regression. Both were reverted.

Also retracted: the derived claim that this and the cranelift bug shared a
**"MIR/HIR-level root, therefore backend-independent"**. The shared-root
conclusion was reasoning built on the retracted mechanisms. (The *observation*
that both backends show symptoms is still true and is explained better by the
stub: a fail-open link is backend-independent for the trivial reason that both
backends emit calls to the same `rt_*` symbols.)

**All original receipts stand.** They were correct observations of real
corruption; only the mechanism attributed to them was wrong. This is why the
receipts are retained verbatim below.

## Original receipts (correct observations, retained)

Guest proof by elimination — outer read correct, inner reads zero:

```
[web-style-producer] buckets-entry    rule_count=26 decls=26
[web-style-producer] buckets-internal class_keys=0 tag_keys=0 fallback=0 bound_class=0
```

`fn _css_scan_rules_simple(css: text) -> CssRuleScan` at
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:287`
(`class CssRuleScan`, line 9, is three `[text]` fields) — inside the callee,
immediately before its return:

```
scan-internal np=27 out=26
```

In the caller, immediately after the call:

```
scan-returned candidates=0 decl_arr=0 wrap_arr=0
```

Callee body inlined into the caller frame, no other change:

```
scan-returned candidates=26 decl_arr=26 wrap_arr=26
rules-total decls=26
```

Inlining "worked" because it removed a copy path, not because it removed a
return boundary.

## Causal chain (worked example, end to end)

1. `rt_array_copy` binds to a weak stub returning 0
2. → every array-place-alias copy yields an un-tagged 0 word
3. → the inline element reader sees `tag != 1`, leaves default `$0x3` nil
4. → `.len()` reads 0 → `bucket_capacity` computes 0
5. → selector buckets allocated empty (`class_keys=0 tag_keys=0 fallback=0`)
6. → node matches 0 of 26 CSS rules
7. → no theme styles applied → `bg=0`, backdrop empty
8. → material witness admits nothing
9. → `content-provenance-rejected` on all 3 WM windows
10. → `guest-render-fault` → SimpleOS-WM x QEMU showcase cell red

Steps 1-4 are silent. The first visible symptom is six steps downstream of the
cause, in an unrelated subsystem. That distance is the whole reason two wrong
compiler mechanisms looked convincing.

## THE SYSTEMIC FINDING — this is the real fix

**The Rust seed's linker already guards against exactly this.**
`src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:474-505`
(`check_no_fake_rt_stubs`, task #97) refuses fabricated `rt_*` stubs, with a
comment that reads as a prophecy of this incident:

> A fake stub for a genuine ABI symbol is indistinguishable from a real one at
> link time — it links clean and only crashes (or misbehaves) the first time
> it's actually called, which is exactly the failure mode that burned
> `rt_get_host_target_code` and `rt_value_print` (#93).

**The pure-Simple SimpleOS link path has NO equivalent guard.** That gap is why
this shipped silently, and closing it is the real fix — not chasing symbols one
at a time.

**Audit result: 36 more non-accelerator `rt_*` symbols are still fabricated**,
including **10 `rt_font_*` symbols in a WM that renders text**. Every one is a
live silent-corruption site of the same class. Expect more downstream mysteries
until the guard lands.

## Diagnostic recipe (cheap, general — use this first)

Find fail-open stubs in any freestanding image:

```sh
nm <kernel.elf> | awk '$2=="W" && $3 ~ /^rt_/'
```

then disassemble each candidate and look for the unconditional-zero body:

```
xor %eax,%eax; ret
```

This is minutes of work and would have short-circuited the entire
compiler-mechanism investigation. **On any "data is silently zero/empty in the
guest but fine hosted" symptom, run this before reading compiler source.**

## Cheap verification technique (adopt generally)

To prove a codegen change does *anything* before spending a ~30-minute guest
lane run: build any module with **`--emit-archive` for
`--target x86_64-unknown-none` (~6s)** and inspect `nm -u` / relocations, or
diff archives between two compilers. Byte-identical archives prove the change
never reaches the path — which is precisely how the two retracted mechanisms
were falsified, at ~6 seconds per test instead of 30 minutes. The same recipe
independently cracked the `text.starts_with` miscompile (see Related).

**Two `objdump` traps that produced a wrong conclusion during this campaign:**

- `objdump` prints **relative call targets WITHOUT an `0x` prefix**, so
  pattern-matching on `0x` misses them.
- Calls are emitted as **`movabs $addr,%reg; call *%reg`** — an indirect call
  through a register. **Searching the disassembly for `call <symbol>` finds
  nothing**, which produced one confident and completely wrong "this code is
  never called" conclusion.

Grep **relocations**, not disassembly text, when asking whether a symbol is
referenced.

## Proper fix

**Still open, and it is the whole point of this doc.** The 14 symbols fixed so
far were found one incident at a time; the mechanism that let them ship is
untouched.

1. **Port the seed's `check_no_fake_rt_stubs` guard to the pure-Simple
   SimpleOS link path.** A fabricated stub for a genuine ABI symbol must fail
   the link, with an `RT_KEEP`-style allowlist for deliberate bootstrap
   placeholders — matching the seed's design. **The allowlist must enumerate
   symbols explicitly, never match on prefix** (see the
   `rt_engine2d_simd_*` near miss above).
2. **Implement, or explicitly allowlist, the remaining fabricated
   non-accelerator `rt_*` symbols**, prioritising the 10 `rt_font_*` in a WM
   that renders text. (36 were outstanding at audit time, before the 14
   landed above.)
3. **Regression:** assert no weak zero-returning `rt_*` symbols in the linked
   guest kernel ELF (the `nm` + `objdump` recipe above, as a check script).
4. **Adopt differential testing for every freestanding runtime function**
   against its hosted twin — the technique that caught the `rt_array_copy(nil)`
   deref the lane missed.

**Do NOT weaken a gate or a test.** Project rule. And note the inverse lesson
here: `auto_stubs.c` *is* a weakened gate — a fail-open default that traded a
loud link error for silent wrong answers. That trade is what cost this
investigation two false mechanisms and a guest lane campaign.

## Related

- `doc/08_tracking/bug/text_starts_with_miscompiled_to_bytespan_name_collision_2026-07-27.md`
  — **separate root cause for the remaining guest fault** found in the same
  campaign: `text.starts_with()` binding to `ByteSpan.starts_with` via
  name-only HIR method resolution. Independent defect; both had to be fixed.
  Shares the `--emit-archive` and `objdump` notes above.
- `doc/08_tracking/bug/cranelift_native_aggregate_return_nil_receiver_hosted_wm_2026-07-26.md`
  — overlapping receipts. Its cranelift attribution and the later
  "shared MIR/HIR root" hypothesis are both superseded by this doc.
- `src/compiler_rust/compiler/src/linker/native_binary/stubs.rs:474-505` — the
  guard that exists on the seed path and is missing here (tasks #93, #97).
- `src/runtime/runtime_native.c:3895-3908` — the real `rt_array_copy`, whose
  comment already documented this corruption class from an earlier incident.
- `doc/08_tracking/bug/native_theme_package_aggregate_return_nil_2026-07-24.md`,
  `doc/08_tracking/bug/native_engine2d_readback_aggregate_abi_2026-07-26.md`
  — earlier "aggregate is nil/empty" reports; worth re-checking against the
  fail-open-stub hypothesis before trusting their stated mechanisms.

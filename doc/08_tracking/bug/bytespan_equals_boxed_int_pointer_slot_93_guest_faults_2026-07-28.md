# ByteSpan.equals faults 93x on a boxed integer in a pointer slot (SimpleOS WM guest)

- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- Filed: 2026-07-28
- Gate: `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`
- Baseline symptom: `reason=guest-render-fault`, `serial_log_bytes=31702`,
  93 exception frames, all five markers 0
- ELF analysed: `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`
  (built 2026-07-28 10:40:18)

## Summary

`text.starts_with(...)` is mis-dispatched by MIR lowering to the **struct**
method `ByteSpan.starts_with`. Eight distinct CSS/HTML text functions call the
ByteSpan entry point with `text` receivers. `ByteSpan.equals` then reads
runtime-object header words through `ByteSpan` field offsets, pulls a
non-pointer value into the `data` slot, and dereferences it.

The distinctive `N<<32` register shape is **not** a boxing tag. It is a runtime
object header whose `u32` field at `+0x4` lands in the high dword of a 64-bit
field read at `+0x0`, with the `u32` at `+0x0` cleared by the pointer-tag mask.

## PROVED (disassembly, `objdump -d -m i386:x86-64`)

### 1. ByteSpan field offsets

`ByteSpan {data, off, span_len}` is laid out with **no header**:

    data     @ +0x00
    off      @ +0x08
    span_len @ +0x10

Evidence in `lib__common__bytes__span__ByteSpan_dot_equals` (`0x8024178`, 832 B):

    80241bb: mov  0x10(%rdi),%rdx    ; self.span_len
    80241ed: cmp  0x10(%r8),%rdx     ; other.span_len
    802429e: mov  (%rcx),%rsi        ; self.data      <-- offset +0x0
    80242cb: mov  0x8(%r10),%rax     ; self.off

### 2. The fault site

    802429e: mov  (%rcx),%rsi              ; %rsi = self.data (array handle)
    80242d6: and  $0xfffffffffffffff8,%rsi ; strip pointer tag
    80242da: mov  0x8(%rsi),%rcx           ; FAULT cr2=0x1400000008 (array len)
    8024306: mov  0x18(%rsi),%r10          ; FAULT cr2=0x1400000018 (array data ptr)

`+0x8` / `+0x18` are `RtCoreArray.len` / `RtCoreArray.data`. So `%rsi` holds a
`ByteSpan.data` value that is not a valid `[u8]` handle.

**Nil-check asymmetry (secondary defect):** `self.data` IS nil-checked
(`test %r10,%r10; jne`, panic path at `0x80242b1`). `other.data` at `0x80242d6`
is **not** — it goes straight from the tag mask to the load. A nil `data` on the
`other` side would fault instead of producing the intended diagnostic.

### 3. The mis-dispatch — 8 call sites, `movabs` + indirect call

`ByteSpan.starts_with` is at `0x80244b8`. It is never reached by a direct
`call`; every caller materialises the address first, which is why a
`call <symbol>` grep reports "never called":

| Caller | refs |
|---|---|
| `dom_color__parse_color_value` | 4 |
| `style_block_parse__sb_background_shorthand_color_value` | 7 |
| `..._renderer_style___bg_layer_is_direction` | 4 |
| `..._renderer_declarations__apply_decls` | 2 |
| `..._renderer_foundation__normalize_overflow_box_alignment` | 2 |
| `..._renderer_foundation__parse_linear_gradient_color` | 1 |
| `nogc_sync_mut__ui__theme_package___wm_window_gradient_from_css` | 1 |
| `os__tools__pkg__pkg_repository__load_repositories` | 3 |

**Every one of these takes a `text` parameter**, e.g.
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl:470`
`fn _bg_layer_is_direction(part: text) -> bool`.

### 4. Same source line, two different lowerings — the decisive receipt

Source (`_bg_layer_is_direction`):

    val p = part.trim().lower()
    if p.starts_with("to ") or p == "top" or ...

Emitted (`0x816aaa0`):

    816aab6: call *%rcx                 ; rt_string_trim   -> text
    816aac5: call *%rcx                 ; rt_string_to_lower -> text, %r13 = p
    816aad6: movabs $0x8011f70,%rcx     ; rt_string_new_literal("to ", 3)
    816aae0: call *%rcx
    816aae2: movabs $0x80244b8,%rcx     ; <-- ByteSpan.starts_with
    816aaec: mov  %rax,%rsi             ;     arg1 = text literal
    816aaef: mov  %r13,%rdi             ;     arg0 = text p
    816aaf2: call *%rcx                 ; <-- MIS-DISPATCH: two texts

Twenty bytes later, `p == "top"` on the *same* value lowers correctly:

    816ab16: movabs $0x8005b40,%r8      ; rt_native_eq
    816ab26: call *%r8

Both operands are `text`. Only the `starts_with` predicate is mis-routed.

### 5. Consumer chain

`ByteSpan.starts_with` (`0x80244b8`) reads `0x10(%rdx)` — for a text receiver
that offset is `RtCoreString.data[]`, i.e. **the first 8 characters of the
string** used as `span_len`. It then calls `ByteSpan.slice` (`0x8023fe0`) and
`ByteSpan.equals` (`0x8024574`). `slice` copies `self.data` from offset `+0x0`
of the receiver into a genuine freshly-allocated ByteSpan, so the malformed
value reaches `equals` through a structurally valid object.

### 6. The `N<<32` shape — arithmetic, and RtCoreString ruled out

`src/runtime/runtime_native.c:784` and `:791`:

    typedef struct RtCoreString {        typedef struct RtCoreArray {
        uint32_t kind;      // +0x0         uint8_t  kind;               // +0x0
        uint32_t reserved;  // +0x4         uint8_t  flags;              // +0x1
        uint64_t len;       // +0x8         uint16_t reserved;           // +0x2
        char     data[];    // +0x10        uint32_t transient_scope_id; // +0x4
    } RtCoreString;                         int64_t  len;                // +0x8
                                            int64_t  cap;                // +0x10
                                            void*    data;               // +0x18
                                        } RtCoreArray;

Reading 8 bytes at `+0x0` of either header as a 64-bit `ByteSpan.data`, then
applying `and $~7`, yields `(u32 at +0x4) << 32` whenever the `u32` at `+0x0`
is `<= 7`. That is exactly the observed `N<<32` with a zero low dword — the
tag mask is what clears the low field. It is **not** an integer-boxing tag
(`v<<3`); the `<<32` is pure struct-offset aliasing.

**RtCoreString is RULED OUT as the misread object.** `rt_string_new_uncached`
sets `s->reserved = 0` unconditionally, so a misread string would give
`data == 0` after masking, which hits the explicit nil-check and the `ud2`
panic path at `0x80242b1` — a diagnostic, not a page fault. The 93 frames are
page faults at `0x14000000{08,18}`, so the misread object has a **non-zero u32
at +0x4**. In `RtCoreArray` that field is `transient_scope_id`.

N in {19, 20, 23, 25} are therefore **transient scope IDs**, not loop indices
and not string lengths. (A prior session read them as loop indices because
`k=15, np=24` were nearby; that reading is superseded.)

## INFERRED (not proven)

- The precise MIR guard that fails. `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:611-635`
  builds `predicate_receiver_is_text`, and line 1533 only takes the
  `rt_string_starts_with` path when
  `resolution_is_unresolved or predicate_receiver_is_text`. Recovery is gated
  by `predicate_owner_recovery_allowed = resolution_is_unresolved or
  resolution_is_instance_method` (line 616). A receiver already resolved to
  `ByteSpan.starts_with` under any *other* resolution kind skips the whole
  recovery block, leaves `predicate_receiver_is_text = false`, and falls
  through to the resolved struct method. Not confirmed by instrumentation.
- Which of the 8 call sites produces the 93 frames. All 8 are structurally
  capable of it.

## RULED OUT

- Fabricated/weak stub — `ByteSpan.equals` has a real 832-byte GLOBAL body.
- Stale object cache — cold rebuild (`688 compiled, 0 cached`) reproduced identically.
- The engine2d vtable fix and the `DECODE_INT` arithmetic-shift fix — both ELFs
  disassemble byte-identically at the fault site.
- `reset_function_local_tracking` (landed 2026-07-25,
  `src/compiler/50.mir/_MirLowering/function_lowering.spl:44`) — it names this
  exact failure ("CSS `text.starts_with` dispatched to `ByteSpan.starts_with`
  in SimpleOS"), but the 2026-07-28 ELF still contains the mis-dispatch, so the
  per-function local reset is **necessary but not sufficient**.
- Guest-reported `rip` — unreliable (7 distinct RIPs, three mid-instruction).
  All analysis above is static.

## Reproduction

    objdump -d -m i386:x86-64 build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf

`objdump -d` without `-m i386:x86-64` yields plausible-looking garbage — the
ELF header says ELF32 while the code is x86-64. `readelf` awk parsing has also
mis-resolved symbols on this binary. Confirm the mis-dispatch with:

    objdump -d -m i386:x86-64 <elf> | grep -n 'movabs \$0x80244b8'

Eight callers, 24 references, zero direct `call 80244b8` instructions.

## Suggested fix direction

Make the MIR predicate path authoritative on the receiver's MIR type rather
than on resolution kind: if `local_is_str(receiver)` is true, `starts_with` /
`ends_with` / `contains` must lower to `rt_string_*` regardless of what HIR
resolution already bound. Separately, restore the missing nil-check on
`other.data` in `ByteSpan.equals` codegen so a malformed span reports instead
of faulting.

Verify any candidate patch is not a no-op before a lane run:

    --emit-archive --target x86_64-unknown-none   # ~6s/module, byte-compare archives

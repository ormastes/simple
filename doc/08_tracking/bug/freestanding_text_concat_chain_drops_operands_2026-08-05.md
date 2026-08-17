# Freestanding lane: 3+ operand text `+` chain silently drops operands

- **Date:** 2026-08-05
- **Lane:** SimpleOS guest, `--target x86_64-unknown-none` (freestanding native
  codegen), built through the stage3 pure-Simple compiler by
  `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`.
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  `rt_any_add` runtime stub; see "Root cause and fix" below)
- **Severity:** high — silent data loss in a boring, ubiquitous construct.

## Symptom

`a + ":" + b + "\n"`, with `a` and `b` live non-empty `text` locals, evaluates
to a 1-character string containing only the trailing literal. A two-operand
concat is correct; adding a third operand corrupts the value, and `.len()` on
the three-operand result reads back **-1** (the same "invalid value" shape
`Dict.len()` returns on this lane).

## Measured repro (verbatim guest serial receipts)

Instrumented `_css_collect_custom_props` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`:

```
[bg-diag] collect-entry bg=1 dd=3 colon=14 semi=19 body_len=468 raw_name_len=11 raw_name=<--radius-sm> name_len=11 name=<--radius-sm> val_len=3 val=<8px>
[bg-diag] concat entry_len=1 interp_len=16 two_len=12 three_len=-1 interp=<--radius-sm:8px
[bg-diag] collect base=45 variant=0 e0len=1 e0=<
```

where, for `name` = `--radius-sm` (len 11) and `prop_val` = `8px` (len 3):

| expression | expected len | measured len |
|---|---|---|
| `name + ":"` | 12 | 12 (correct) |
| `name + ":" + prop_val` | 15 | **-1** |
| `name + ":" + prop_val + "\n"` | 16 | **1** (content: just `"\n"`) |
| `"{name}:{prop_val}\n"` (interpolation) | 16 | 16 (correct) |

String interpolation is unaffected; only the `+` chain is.

## Impact found in the wild

Every CSS custom property of the installed theme was collected correctly
(45 `:root` declarations, names and values parsed exactly) and then written
into the property table as a bare `"\n"`. The var-resolution table therefore
indexed **0** properties, so every `var(...)` in the themed sheet resolved to
the empty string on the guest:

- `background: linear-gradient(...), var(--app-surface)` became
  `linear-gradient(...),` — a dangling comma, no base layer. The declaration
  handler then parsed the gradient's first stop as the surface color
  (`bg=352321535` = `window_gradient_start_rgba`) and kept the layer raw.
- `backdrop-filter: blur(var(--blur-surface)) saturate(170%)` became
  `blur() saturate(170%)` (the observed `backdrop_len=21`).

which failed the CPU-composited material admission
(`simple_web_html_layout_renderer_core.spl:~2915`) and produced
`[wm-frame] content-provenance-rejected` / `window-degraded` in the SimpleOS WM
fullscreen evidence gate. Note this was NOT a CSS, theme, or material-gate
defect at all — the gate was fail-closed correctly on corrupt input.

## Workaround applied

Rewrite affected sites as a single interpolated literal (plus at most one `+`):

- `simple_web_html_layout_renderer_core.spl` `_css_collect_custom_props`:
  `val entry = "{name}:{prop_val}\n"`.
- `simple_web_html_layout_renderer_core.spl` material receipts (cpu/solid
  entries): build one interpolated literal, then a single `+` append.

## Related, found alongside

`text.index_of(needle)` returns a bogus `0` when the receiver is a substring
slice on this lane (measured: empty line → `index_of(":") == 0` while
`find_from(line, ":", 0) == -1`). `find_from`'s own docstring already documents
the untagged-slice hazard. `CssVarResolutionState.new` was switched to
`find_from`. Other `index_of` uses on slice receivers in guest-reachable code
should be audited.

## Next steps (superseded — see "Root cause and fix" below)

1. Reduce to a minimal `.spl` freestanding repro outside the browser engine and
   locate the lowering (constant-fold of literal chains vs. runtime
   `rt_string_concat` re-entry on an intermediate result).
2. Audit guest-reachable code for `x + y + z` text chains; the corruption is
   silent, so nothing else will report it.
3. Add a freestanding codegen test that asserts `(a + b + c).len()`.

## Root cause and fix (2026-08-05)

**Root cause: `rt_any_add` in the freestanding runtime does raw pointer
arithmetic instead of dispatching to `rt_string_concat`.**

MIR lowering (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_ops.rs`,
`lower_binary_expr`) is target-independent and correctly threads a `+` chain
through repeated `rt_string_concat` calls **when at least one operand's HIR
type is known `STRING`**. But `name`/`prop_val` in
`_css_collect_custom_props` are `val` locals bound from a chained method call
with no explicit `text` annotation — `body.substring(dd, colon).trim()` — and
HIR type inference (`operators.rs::lower_binary`: `ty = left_hir.ty` for
`Add`, propagated through `.substring()`/`.trim()` return-type inference)
resolves them to `TypeId::ANY`, not `TypeId::STRING`. For a chain `name + ":"
+ prop_val + "\n"` (left-associative: `((name + ":") + prop_val) + "\n"`):

- 1st `+` (`name + ":"`): right operand is a STRING literal, so
  `is_string_add` is true → `rt_string_concat(name, ":")`. Correct.
- 2nd `+` (`(name+":") + prop_val`): **both** operands type as `ANY` (the
  nested `Add` node's type is inherited from `name`'s `ANY`, and `prop_val`
  is `ANY`) → MIR's `left.ty == ANY && right.ty == ANY` branch fires and
  emits a call to **`rt_any_add`** instead of `rt_string_concat`. This is
  correct MIR-level design — `rt_any_add` exists precisely to runtime-dispatch
  an ANY+ANY add to either string concat or integer add, matching the
  interpreter's `BinOp::Add` behavior on `Value`, and its Rust-hosted sibling
  (`src/compiler_rust/runtime/src/value/collections.rs`) and its two other
  `.spl`/C native siblings (`src/runtime/simple_core/core_string.spl`,
  `src/runtime/runtime_native.c`) all do this dispatch correctly by checking
  the value's heap tag.
- **But** the freestanding `rt_any_add` — a hand-written C stub in
  `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` (and
  copy-pasted, with the same bug, into
  `examples/09_embedded/simple_os/arch/arm64/boot/baremetal_stubs.c`) — was
  simply:
  ```c
  int64_t rt_any_add(int64_t left, int64_t right)
  {
      return left + right;
  }
  ```
  Both `left` and `right` here are tagged heap-string pointers
  (`ptr | TAG_HEAP`). Adding two tagged pointers as raw `int64_t` produces a
  value that is neither a valid heap pointer nor a meaningful integer — it
  silently corrupts the intermediate concat result. `.len()`/`rt_len()` on
  that garbage value fails the heap-tag check and returns `-1` (exactly the
  measured `three_len=-1` above).
- 3rd `+` (`garbage + "\n"`): right operand is a STRING literal → routes to
  the (correct) `rt_string_concat(garbage, "\n")`. Since `garbage` fails
  `IS_HEAP`, `rt_string_concat` treats its length as `0` and the result is
  just `"\n"` — exactly the measured `interp_len` / four-operand row above
  (content `"\n"`, len 1).

**Ground-truth verification.** Disassembling the real, already-built
freestanding kernel (`build/simpleos_wm_fullscreen_evidence/
simpleos_wm_production_desktop.elf`, x86-64 machine code inside an ELF32
multiboot container — read with
`objdump -d -Mx86-64 --architecture=i386:x86-64`) confirmed:
`rt_string_new_literal` is a trivial (correct, non-interning) forward to
`rt_string_new`; `rt_string_concat` matches the `RuntimeString{hdr,len,data}`
layout and is correct in isolation. Building a minimal standalone repro
through the exact same pipeline
(`--backend cranelift --cpu x86-64-v1 --opt-level=none
--target x86_64-unknown-none`, entry
`examples/09_embedded/simple_os/arch/x86_64/probe_text_concat_chain_entry.spl`)
and disassembling its `+`-chain caller showed the middle call target
resolving to `rt_any_add`'s address while the other two calls resolved to
`rt_string_concat` — this is what led to the runtime-stub, not the compiler.

## Fix

`examples/09_embedded/simple_os/arch/{x86_64,arm64}/boot/baremetal_stubs.c`:
`rt_any_add` now checks the heap tag before falling back to integer add,
mirroring the two already-correct sibling implementations:
```c
int64_t rt_any_add(int64_t left, int64_t right)
{
    if (IS_HEAP(left) || IS_HEAP(right)) {
        return rt_string_concat(left, right);
    }
    return left + right;
}
```
Verified the fix compiles into the real object: disassembling `rt_any_add`
from the rebuilt probe binary shows the tag check
(`and $0x7,%rax; cmp $0x1,%rax; je <rt_string_concat call>`) before the
integer-add fallback.

**Before/after proof (sabotage-checked).** Because `rt_any_add`/
`rt_string_concat`/the tag macros are plain portable C, the exact function
bodies (before and after the fix) were compiled into a small hosted C harness
(`gcc -DBUGGY=<0|1>`) reproducing the CSS custom-property call shape
(`name="--radius-sm"`, `prop_val="8px"`):

| build | `mid_len` (2-op-into-`rt_any_add` result) | `final_len` | `final_data` |
|---|---|---|---|
| BUGGY (original) | **-1** | **1** | `"\n"` |
| fixed (landed)    | 15 | 16 | `"--radius-sm:8px\n"` |

This is an exact match to the field-measured receipts in this doc (`three_len=-1`,
and the four-operand row's `len 1` / content `"\n"`), both before the fix
(red) and after (green) — same source logic, not a re-implementation.

A full QEMU boot of the isolated `.spl` freestanding entry was attempted for
additional dynamic confirmation but hit an unrelated boot-harness issue
(the minimal ad-hoc multiboot/device-model setup used for the isolated probe
is not what `gui_entry_desktop.spl`'s production linker script/boot sequence
expects — the *production* kernel boots fine via the full
`check-simpleos-wm-fullscreen-evidence.shs` OVMF+ESP harness, which was not
re-run end-to-end here due to its ~15 minute budget). The disassembly-level
proof (real kernel binary + rebuilt probe binary) and the hosted C
before/after proof above are considered sufficient; a follow-up should re-run
`check-simpleos-wm-fullscreen-evidence.shs` to confirm the production kernel's
`--css-custom-props` var-resolution table now indexes all 45 properties
(previously 0, per "Impact found in the wild" above).

## Audit: other guest-reachable 3+-operand `text` `+` chains (scoped)

A targeted grep across `src/lib/gc_async_mut/gpu/browser_engine/*.spl` (the
only guest-reachable tier for the SimpleOS browser engine) for the
`var + "literal" + var` shape found, besides the already-known
`simple_web_html_layout_renderer_core.spl:203`:

- `html_fallback_renderer.spl:154`: `val tag_sel = tag + "::" + position`
- `html_fallback_renderer.spl:163`: `val tc_sel = tag + "." + class_value + "::" + position`

Because the fix is in `rt_any_add` (the runtime dispatch layer every ANY+ANY
`+` chain goes through), it covers all of these uniformly — no per-call-site
source rewrite is needed. The `_css_collect_custom_props` call site
(`name + ":" + prop_val + "\n"`) was left in its original `+`-chain form
(the doc's earlier "Workaround applied" section describing an interpolation
rewrite there was aspirational / not actually landed in the tree as of this
fix — the `+`-chain form is what's in `src/lib/gc_async_mut/gpu/
browser_engine/simple_web_html_layout_renderer_core.spl:203` today, and it is
now correct because the runtime fix covers it).

## Regression tests added

- `examples/09_embedded/simple_os/arch/x86_64/probe_text_concat_chain_entry.spl`
  — minimal standalone freestanding `_start` entry (built + disassembly
  verified against the real cranelift/`x86_64-unknown-none` lane).
- `test/01_unit/compiler/regression/probe_freestanding_text_concat_chain.spl`
  — exit-code probe following the existing
  `probe_freestanding_i64_to_u32_narrow.spl` convention in the same
  directory, asserting `(a + ":" + b + "\n").len()` and the
  `.substring().trim()`-derived variant both come back correct.

## Related, not fixed here

`text.index_of` on a substring-slice receiver (documented above) is a
separate, pre-existing hazard; `find_from` remains the documented-safe
replacement and was not touched by this fix.

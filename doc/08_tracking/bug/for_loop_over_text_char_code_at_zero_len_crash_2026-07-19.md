# BUG: `for ch in <text>:` loop-bound element is corrupted — `char_code_at(0)` always 0, `.len()` segfaults the interpreter

## Status
Open (2026-07-19, GLYPH-FIX-7 campaign). Root-cause LOCALIZED, not yet fixed.
Distinct from, and upstream of, both:
- `native_char_code_at_tag_shift_2026-07-19.md` (FIXED, c97697506aa) — that bug
  was `text.char_code_at(i)` called DIRECTLY on a multi-char receiver returning
  a `>>3` tag-shifted value. That fix is real and confirmed still correct (see
  Evidence below); it does NOT cover this bug.
- `x64_freestanding_char_code_at_dynamic_text.md` (Open) — scoped to
  freestanding-only, dynamically-built (`rt_string_from_byte_array`) text at
  SCATTERED indices. This bug reproduces on a plain **string literal**, in
  **both** the hosted interpreter and the freestanding native-build, and is
  specifically about the **for-loop-produced element**, not the source text's
  construction method.

## Summary
`for ch in <any text value>: ch.char_code_at(0)` always returns codepoint
**0**, for every character, regardless of whether the source text is a
literal or dynamically built (string interpolation/concatenation). The SAME
text decoded via explicit indexing (`text.char_code_at(i)` in a `while`
loop, or a one-off `text.char_at(i)` outside any loop) decodes **correctly**.
Additionally, calling `.len()` on the for-loop-bound element **segfaults the
seed interpreter** (core dump) — a distinct, more severe symptom than the
silent-wrong-value case, but the same underlying corrupted/invalid binding.

This is the direct root cause of the SimpleOS freestanding glyph-rendering
blocker (font pipeline receives correct string LENGTHS but every character
decodes as codepoint 0 → every glyph is the degenerate 0x0 `.notdef` →
zero quads produced for all text draws). `font_renderer.spl`'s
`_prepare_text_active` fallback loop (`for ch in content: val codepoint =
ch.char_code_at(0)`) and `measure_text_width` (same idiom) both hit this bug
for every one of SimpleOS's 7 live text commands (window titles, taskbar
labels, clock).

## Reproduction

### Freestanding (Cranelift, x86_64-unknown-none)
`examples/09_embedded/simple_os/arch/x86_64/char_code_at_loop_probe_entry.spl`
(new minimal probe, no nvme/net/vmm deps — ~7s build, ~20s boot via
`isa-debug-exit`). Builds a text via the SAME nested-interpolation pattern
`host_taskbar_clock_label` uses (`"{hour_text}:{minute_text}"` where the
parts are themselves `"0{n}"`-style interpolations), plus a plain literal
control `"09:05"`. Serial output (both `--opt-level=aggressive` and
`--opt-level=none` — identical, ruling out an optimization-pass artifact):

```
[probe] dynamic_text len expected=5 actual=5
[probe] dynamic idx=0 cp=0   ... idx=4 cp=0        <- nested-interp text, ALL wrong
[probe] literal_text len expected=5 actual=5
[probe] literal idx=0 raw_bits=209 cp=0 ch_len=-1 ch_len_raw=1153202240580812627 ch_raw_char_at=134310129
...                                                  <- literal text, ALL wrong, raw bits implausible
[probe] noloop_charat0 raw_bits=134316737 cp=48 d_len=1 d_len_raw=1   <- SAME literal, char_at(0) OUTSIDE a loop: CORRECT
[probe] indexed idx=0 cp=48 ... idx=4 cp=53                          <- SAME literal, explicit-index while-loop: CORRECT
```

`raw_bits` (captured via a diagnostic `rt_probe_raw(v) -> v` passthrough,
since reverted — see Cleanup) decode with `TAG_HEAP` (low 3 bits `001`) but
to implausibly tiny addresses (0xD1, 0x31, 0x71, 0xA1, 0x01 stripped) — not
valid heap pointers, and the value **changes between separate builds of
identical source** (209/49/113/161/1 vs 177/17/81/145/241 on a rebuild),
indicating uninitialized/stack-dependent memory, not a deterministic
tag-shift.

An explicit-typed-intermediate workaround (`val ch2: text = ch` before
calling methods — the project's documented "erased receiver" mitigation,
`.claude/rules/language.md`) does **not** help: `ch2`'s raw bits are
bit-for-bit identical to `ch`'s. This rules out method-dispatch-on-erased-
type as the mechanism; the value itself is already wrong at first read.

### Hosted (interpreter, same seed binary, `run` subcommand)
```simple
fn main():
    val lit = "09:05"
    var i = 0
    for ch in lit:
        val cp = ch.char_code_at(0)
        print("loop idx={i} cp={cp}")   # -> cp=0 for every i (WRONG)
        i = i + 1
    var wi = 0
    while wi < lit.len():
        val cp2 = lit.char_code_at(wi)
        print("indexed idx={wi} cp={cp2}")  # -> 48,57,58,48,53 (CORRECT)
        wi = wi + 1
```
Confirms the bug is **not** freestanding-specific: it reproduces identically
in the hosted interpreter, so the defect lives in code shared by both
execution modes (HIR-level for-loop desugaring/typing, or a helper both the
interpreter and MIR lowering call through).

**Crash (new finding):** replacing `ch.char_code_at(0)` with `ch.len()`
inside the SAME for-loop **segfaults the interpreter** (`timeout: the
monitored command dumped core`), even in isolation (`print("l={ch.len()}")`
alone, no other calls on `ch`). This did not reproduce when only
`char_code_at(0)` was called. This means `ch`'s underlying `Value::text` is
not merely holding a wrong scalar — some accessors on it access invalid
memory outright.

**Decisive follow-up: `ch` ITSELF is corrupted, not just accessors on it.**
`for ch in lit: print("idx={i} ch={ch}")` — interpolating `ch` directly,
with NO method call on it at all — prints `33`, `97`, `225`, `193`, `161`
for the five characters of `"09:05"`, i.e. small integer-looking values,
not the characters and not their ASCII codes (48/57/58/48/53) either. This
rules out "the loop produces a valid `ch` and only `char_code_at`/`len`
misconsume it" — the bound value is already wrong at the point of
production/binding, before any method dispatch happens. Points at
`bind_pattern`/`Env` storage in `exec_for`
(`interpreter_control.rs:3228-3313`) over the `iter_to_vec` production step
(`interpreter_helpers/collections.rs:403`, which looks correct on
inspection) as the more likely fault site.

## Root-cause candidates (not yet pinned to a single line)

1. **Interpreter (`src/compiler_rust/compiler/src/interpreter_control.rs`,
   `exec_for` ~L3228-3313):** uses `iter_to_vec(&iterable)` to build the
   full `Vec<Value>` up front, then `bind_pattern` per iteration.
   `iter_to_vec`'s `Value::Str` arm
   (`src/compiler_rust/compiler/src/interpreter_helpers/collections.rs:403`)
   — `s.chars().map(|c| Value::text(c.to_string())).collect()` — looks
   correct on inspection (produces owned, independent `Value::text` per
   char). The corruption must therefore be introduced later: in
   `bind_pattern`'s env-slot handling, or in how the loop-variable binding's
   lifetime interacts with the `Value::text` payload's storage across
   iterations (dangling/aliased reference; the segfault on `.len()` is
   consistent with a use-after-free-class bug, not a simple wrong-value bug).

2. **MIR/Cranelift lowering (`src/compiler_rust/compiler/src/mir/lower/
   lowering_stmt.rs` ~L1272-1565, generic "index-based iteration over
   collections"):** computes `element_ty` by matching
   `HirType::Array { element, .. }` against the iterable's HIR type
   (`registry.get(iterable.ty)`). A `text` iterable's type is the SEPARATE
   `HirType::String` variant (`hir/types/type_system.rs:176`), which never
   matches the `Array` pattern, so `element_ty` silently falls back to
   `TypeId::ANY` for every text for-loop. `needs_int_unbox`/
   `needs_float_unbox` both evaluate false for `ANY`, so no unboxing is
   applied to the `IndexGet` (`rt_index_get`) result before it's stored to
   the loop-variable's local slot — this path does NOT explain the observed
   corruption by itself (the stored value should be the raw, correctly-
   tagged `rt_index_get` return), but the `ANY`-vs-`String` type-registry
   miss is real and may matter to a downstream consumer (liveness/GC-root
   tracking, a different Store/Load path than the one inspected, or the
   LLVM backend's parallel `compile_index_get`, not audited here). Confirmed
   NOT an artifact of `--opt-level=aggressive` (identical result at
   `--opt-level=none`), and confirmed `rt_index_get` / `rt_string_char_at` /
   `rt_for_iterable` have exactly one definition each in the linked kernel
   (no weak-stub shadowing — `objdump -t` / `nm` showed one global symbol
   per name, ruling out the `rt_char_from_code`-class "unlinked strong def,
   weak catch-all wins" bug pattern for these specific functions).

3. Given the SAME wrong behavior appears in both the tree-walking
   interpreter and the Cranelift-compiled native path, the shared point is
   most likely upstream of both: HIR construction/type-checking of the
   for-loop's pattern-variable type when iterating a `String`-typed
   collection (only `Array<T>` element-type inference is handled; `String`
   iteration may fall through to an unhandled/erased case that both
   consumers independently mishandle, in different but analogous ways).

## Impact
Every `for ch in <text>: ch.char_code_at(...)` idiom is affected — this is a
common idiom (grep hits in `font_renderer.spl`, and likely elsewhere in
`src/lib`). Confirmed direct impact: 100% glyph-rendering failure for all
dynamic on-screen text in the SimpleOS freestanding desktop kernel
(window titles, taskbar, clock — all 7 live `draw_text` commands verified
via producer/consumer probes to reach `_prepare_text_active` with correct
string lengths but produce 0 quads, root-caused to this bug via the
`char_code_at(0)`-always-0 chain: `has_glyph(0)=true` → rasterize succeeds
→ degenerate 0x0 `.notdef` glyph → filtered out by `glyph.width > 0 and
glyph.height > 0` → empty quad list).

**Fallback-path execution CONFIRMED (not just inferred):** `FontRasterizer`
(`spl_fonts.spl`) resolves `layout_fp`/`layout_glyph_metric_fp` via
`spl_dlsym(h, "rt_fonts_layout_text" / "rt_fonts_layout_glyph_metric")`
(`spl_fonts.spl:235-236`). On this freestanding x86_64 target,
`spl_dlsym`/`spl_dlopen`/`spl_wffi_call_i64` are strongly overridden in
`baremetal_stubs.c` (~L17658-17672) to unconditionally `return 0` — the
target has no dynamic linker, documented in that file's own comment block
("SFFI dlopen-based dynamic loading is inherently unsupported on this
freestanding kernel target"). Therefore `layout_fp == 0` and
`layout_glyph_metric_fp == 0` ALWAYS on this target, so `layout_text()`
(`spl_fonts.spl:531`, `if ... self.layout_fp == 0 ...: return []`) ALWAYS
returns `[]`. This makes `_prepare_text_active`'s `layout.len() == 0`
fallback condition unconditionally true on freestanding, so its
`for ch in content: val codepoint = ch.char_code_at(0)` loop is
unconditionally the live path for every text draw — closing the causal
chain from this bug to the glyph-rendering blocker with certainty, not
inference. (Separately, `has_glyph_fp`/`raster_fp` — used by
`rast.has_glyph()`/`rast.rasterize()` downstream of the fallback loop —
were observed live/non-zero in kernel probes, so SOME SFFI function
pointers ARE populated through a mechanism other than the always-failing
`spl_dlsym`; that discrepancy doesn't affect this chain's conclusion since
the codepoint fed into rasterization is what's corrupted regardless of
which rasterize backend consumes it.)

## Why not fixed in this session
This is a T3-tier defect (shared HIR/interpreter/codegen infrastructure,
`src/compiler_rust`) affecting a pervasive language idiom. A blind patch
risks a broad regression across every `for x in text:` call site in the
compiler and stdlib, and any seed change requires a full bootstrap to
validate (`.claude/rules/bootstrap.md` T3). The mission's ≤3-iteration
budget and single-session scope are not sufficient to safely design,
implement, and full-bootstrap-validate a fix to shared for-loop/String
type-inference or interpreter binding lifetime code. Filing this as a
precise, reproducible, root-cause-localized bug for a dedicated follow-up
session (or a session willing to run the full T3 bootstrap gate) is the
honest, non-cover-up outcome per repo policy.

## Workaround (documented precedent, NOT applied to font_renderer.spl per
mission edit-surface restriction — font_renderer.spl edits are gate-flips
only in this campaign)
Replace `for ch in content: ch.char_code_at(0)` with explicit-index
iteration: `while i < content.len(): val cp = content.char_code_at(i); i =
i + 1`. This is proven correct in both hosted and freestanding modes (see
Reproduction above) and matches the existing workaround pattern already in
use elsewhere in the codebase (`x64_freestanding_char_code_at_dynamic_text.md`'s
`rt_string_to_byte_array` + `rt_bytes_u8_at` idiom is a variant of the same
"avoid for-loop-over-text, index explicitly" principle).

## Repro artifacts
- `examples/09_embedded/simple_os/arch/x86_64/char_code_at_loop_probe_entry.spl`
  (new, minimal, no nvme/net/vmm deps; kept as a standing repro/regression
  probe once a fix lands).
- Hosted repro: run the `fn main(): ...` snippet above via
  `SIMPLE_BOOTSTRAP=1 SIMPLE_LIB=<repo>/src <seed> run <file>.spl`.

## Related
- `doc/08_tracking/bug/native_char_code_at_tag_shift_2026-07-19.md` (fixed;
  different call shape)
- `doc/08_tracking/bug/x64_freestanding_char_code_at_dynamic_text.md` (open;
  freestanding + dynamic-text-only scope, narrower than this bug)
- `doc/08_tracking/bug/for_loop_var_shadows_prior_local_binding_lost_2026-06-11.md`
  (prior, different for-loop local-binding defect class — same general
  "for-loop pattern-variable local slot" area of the compiler)

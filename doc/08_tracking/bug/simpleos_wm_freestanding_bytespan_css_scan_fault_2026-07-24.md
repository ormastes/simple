# SimpleOS WM Freestanding ByteSpan CSS Scanner Fault

## Status

Fix implemented; fresh bootstrap/object and OVMF verification pending. The
previous boot reaches the production desktop compositor and scanout, but no
post-fix framebuffer capture exists yet.

## Evidence

The latest live bounded run is:

`doc/09_report/wm_glass_theme_qemu_postfix2_2026-07-24.md`

The serial log reaches font registration, shell initialization, application
spawn, software-render fallback, NVMe/FAT32 setup, and the 3840x2160 scanout.
It then repeatedly page-faults with the first return address inside:

`simple_web_html_layout_renderer._css_scan_rules_simple`

The faulting instruction is inside:

`common.bytes.span.ByteSpan.starts_with`

Disassembly of the guest kernel proved this was a compiler dispatch error, not
corrupted `ByteSpan` data. `_css_scan_rules_simple` passed its trimmed text
receiver and the literal `"@"` to the address of
`ByteSpan.starts_with`. Many unrelated text call sites had the same target.
The HIR method resolution could retain a stale aggregate owner, while MIR's
text fallback only corrected `Unresolved` calls.

`method_calls_literals.spl` treats MIR/HIR-proven text as authoritative for
`starts_with`, `ends_with`, and `contains`, even when HIR supplied a stale
resolved instance method. Genuine custom struct receivers retain their normal
dispatch. That fixes an explicitly annotated `val opener: text`, but the
production scanner uses the inferred form `val opener = ...trim()`.

A fresh pure-Simple Cranelift bootstrap compiler was built at:

`build/bootstrap-wm-text-dispatch/stage4-cranelift/aarch64-apple-darwin/simple`

Its CSS-shaped collision fixture emitted
`exercise_css_text_owner -> rt_string_starts_with`; the same object separately
defines and calls `CustomPrefixOwner.starts_with`. It has no `ByteSpan`
predicate reference. The executable link was blocked by an existing
`libsimple_runtime.a` Metal-framework linkage gap, after object generation.

That original fixture explicitly annotated `opener: text` and masked the
remaining defect. The fixture now matches production by leaving `opener`
inferred. Three bounded compiler/probe iterations established:

1. Compiler `bc99e6c6...` emits `rt_string_trim`, then branches to
   `CustomPrefixOwner.starts_with` for the inferred result.
2. Broadening resolved-owner recovery beyond instance methods did not change
   the relocation and was reverted.
3. Compiler `95eceb02...`, built after recording text-result HIR provenance
   and consulting it in `local_is_str`, still emits the custom-owner branch.

The final object is retained at:

`build/wm-text-dispatch-inferred-green-v3/native-objects-s8YDv6/mod_0.o`

Despite the directory label, this is RED evidence. Its
`___exercise_css_text_owner+0x294` relocation targets
`___CustomPrefixOwner_dot_starts_with`; there is no
`_rt_string_starts_with` relocation.

Two live QEMU cycles were used. The first used a compiler artifact older than
the final source and was classified stale. The second used compiler
`bc99e6c6...`, kernel `fdf35e19...`, reached the 3840x2160 ARGB scanout, and
faulted in `ByteSpan.equals` called by `ByteSpan.starts_with`, with the call
origin in `_css_scan_rules_simple`. A third QEMU launch was correctly withheld
because the required object preflight remained RED.

## Required next scope

In a fresh session, inspect the MIR let-binding produced for the inferred
`rt_string_trim` result and prove which local ID/type reaches
`lower_method_call`. Fix that canonical type-provenance boundary; do not add a
CSS-source annotation or special-case the renderer. Rebuild one bootstrap
compiler and require:

```text
___exercise_css_text_owner -> _rt_string_starts_with
___exercise_custom_owner -> ___CustomPrefixOwner_dot_starts_with
```

Only after that object gate passes, run the exact resume command:

```bash
env SIMPLE_BIN="$PWD/<fresh-bootstrap-simple>" \
  SIMPLE_BIN_SOURCE=wm-text-dispatch-inferred-type-fix \
  BUILD_DIR="$PWD/build/wm_glass_theme_qemu_postfix3_2026-07-24" \
  REPORT_PATH="$PWD/doc/09_report/wm_glass_theme_qemu_postfix3_2026-07-24.md" \
  sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs
```

Owner: compiler MIR lowering lane. Final reviewer: highest-capability WM/compiler
review after the object gate and QEMU capture. Do not bypass the canonical
parser or replace the themed document with direct rectangles. The full
Aetheric package CSS must remain intact through computed style and layout.

The QEMU verify/fix cap was reached in this session; do not rerun here.

## 2026-07-24 synchronized root-cause correction

The RED v4 executable proved that the explicit-entry fixture path is owned by
the Rust bootstrap compiler, not the dirty pure-Simple MIR candidate. A
focused Rust MIR regression reproduced the exact call list:

```text
CustomPrefixOwner.starts_with
str.split
trim
starts_with
```

The canonical defect is earlier than MIR owner recovery:

- Rust HIR recognized `text.split` as a string method but omitted its
  `[text]` result type.
- It also omitted the string result type for `trim`, `trim_start`, and
  `trim_end`.
- Consequently `parts[0].trim()` degraded to `Any`; the inferred `opener`
  binding faithfully preserved that wrong type and later predicate dispatch
  was vulnerable to suffix-based custom-owner selection.

The bootstrap parity fix is confined to the String instance-method table in
`src/compiler_rust/compiler/src/hir/lower/expr/mod.rs`: `split` now returns an
array of String and the trim family returns String. The regression
`inferred_text_predicate_does_not_reuse_unrelated_custom_owner` simultaneously
requires `CustomPrefixOwner.starts_with` for the real custom receiver and
`str.starts_with` for the inferred CSS receiver. It went RED before the fix
and PASS afterward (1 passed, 3334 filtered out).

Runtime verification remains gated on a fresh Stage 2/3 bootstrap, relocation
proof, canonical hosted WM evidence, and canonical OVMF evidence. Presentation
evidence must also carry and validate the Web render backend plus the realized
solid-material SHA-256; configured theme markers alone are insufficient.

# Native module-level derived `i32` constant is tag-shifted

> **CLAIMED-OFFHOST 2026-08-17** — do not work locally; assigned to a second host. See doc/03_plan/infra/priority_bug.md

- **Observed:** 2026-07-27 on the pure-Simple Cranelift Stage 3 lane.
- **Scope:** focused 300-DPI Engine2D font producer probe.

The typed module-level value

```simple
val FONT_POINTS: i32 = 24
val FONT_DPI: i32 = 300
val FONT_SIZE_24PT_300DPI: i32 = (FONT_POINTS * FONT_DPI + 36) / 72
```

does not compare equal to literal `100` in the generated native probe, even
though the same rounded point-to-pixel formula is mathematically exact.
The build compiled 184 modules with zero failures and the run reached only
`engine2d_font_state_native_status=fail-300-dpi-size`; Bungee load and identity
checks before it passed.

The focused probe keeps the required derivation but moves it to typed
function-local values. This is not evidence that the module-global compiler
defect is fixed. A future compiler regression should compare module and local
derived `i32` values in interpreter and native modes with stub fallback
disabled.

The next native cycle proved the function-local formula itself passes, then
faulted with `field access on nil receiver` before a configured-draw receipt.
The initially suspected aggregate-return boundary was removed from the receipt
path: Engine2D now derives the size and constructs `FontRenderConfig` directly
in the same frame. It stores only the boolean predicate `size == 100`, not the
derived `i32`, across the Engine2D field boundary.

Crash reports from the following two bounded cycles localized the actual fault
earlier, in cache-stat reset verification. Disassembly shows the reset call
receiving the typed `FontRenderer` in `x0`, followed by
`receipt_cache_rasterizations_zero()` with no receiver reload before `blr`.
The source now exposes one atomic mutating `reset_cache_stats_receipt()` call,
while the remaining compiler defect stays open. This adaptation has not
received a fourth native run; the three-cycle cap is exhausted.

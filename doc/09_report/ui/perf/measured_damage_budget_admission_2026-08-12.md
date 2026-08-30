# Measured damage-budget admission — 2026-08-12

Status: mechanism/correctness PASS; profile-specific admission, not an 8K/80
frame proof.

## Result

`common.ui.render_opt.damage_budget` converts an operation profile's measured
7,680-pixel row p95 into an exact maximum dirty-pixel allowance for a requested
frame budget. It consumes the same immutable `DamageFramePlan` used by CPU and
Vulkan, and records the measurement basis in its receipt. Missing or invalid
measurements fail closed; idle frames admit with zero predicted work.

At a 12,500,000 ns budget using the 2026-08-12 native x86 receipts:

| Operation profile | Maximum pixels | 8K fraction | Full-frame projection |
|---|---:|---:|---:|
| opaque constant, 1,503 ns/row | 63,872,255 | >100% | 6.49 ms |
| fill, 1,854 ns/row | 51,779,935 | >100% | 8.01 ms |
| copy, 2,034 ns/row | 47,197,640 | >100% | 8.79 ms |
| opaque image, 12,544 ns/row | 7,653,061 | 23.06% | 54.19 ms |
| mixed-alpha image, 114,549 ns/row | 838,069 | 2.52% | 494.85 ms |

Focused interpreter spec: 4/4 PASS. O3 analysis completed with two low-level
dead-code opportunities and no source-pattern findings.

## Interpretation

This turns frame switching into a falsifiable per-operation condition. A frame
whose mixed-alpha dirty plan exceeds 838,069 pixels cannot claim 80 fps from
this profile even though it is technically "partial". Conversely, a bounded
plan at or below the limit is admitted only as a kernel estimate; executor,
submission, presentation, readback, RSS, fallback, and checksum receipts must
still pass in an end-to-end 8K run.

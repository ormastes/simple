# Draw IR Web renderer live matrix

This operator scenario verifies retained R9 evidence. It never creates default
or synthetic PASS rows. Linux `metal-unavailable` records only an accountable
external-host handoff and does not satisfy the required physical macOS Metal
row.

## Verify retained live evidence

Step: `Verify the live rendering matrix`.

Set `DRAW_IR_LIVE_MATRIX_EVIDENCE` to the retained dotenv receipt and
`DRAW_IR_LIVE_MATRIX_CURRENT_REVISION` to the current 40-character commit or
64-character content revision. Then run the admitted pure-Simple test runner:

```text
DRAW_IR_LIVE_MATRIX_EVIDENCE=<retained.env> \
DRAW_IR_LIVE_MATRIX_CURRENT_REVISION=<current-revision> \
bin/release/simple test test/03_system/app/ui.browser/feature/draw_ir_web_renderer_live_matrix_spec.spl --mode=interpreter --assert-ran --fail-fast
```

The `expect_live_matrix_row` checker requires every Linux row to retain the
current revision, a real binary path whose SHA-256 matches the receipt, positive
warm timing, positive max RSS, and exact parity. CUDA and Vulkan additionally
require a physical device, nonempty driver, positive device identity,
`device_readback`, and `cpu_fallback=false`.
The software and CPU-SIMD rows must label their readback sources
`software_oracle` and `cpu_simd_oracle`; an unlabeled CPU result cannot satisfy
either row.

The bounded strict-stage2 source-fix run remains blocked. The x86_64 AVX2 row
recorded one native SIMD hit and 17 provider hits, but exact readback reported
174 diagram mismatches (`76301990031512` scalar versus `56977497754816`
CPU-SIMD). The process used 2048 KiB max RSS; elapsed time rounded to 0.00
seconds, so the retained warm timing is zero and cannot admit a passing row.
The paired software oracle remains separate and blocked only because its
CPU-SIMD counterpart failed parity.

The Metal blocker must retain `status=unavailable`,
`evidence_class=external-host`, the current revision, and nonempty `owner`,
`prerequisite`, `resume_command`, and `artifact_path` fields. Missing evidence,
a stale revision, a changed binary, CPU fallback, or invocation without
`--assert-ran` fails closed.

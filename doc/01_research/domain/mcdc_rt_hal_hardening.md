# Domain Research: MC/DC, Dynamic Instrumentation, and HAL Comparison

Date: 2026-08-25

## Conclusions

FAA/NASA guidance requires each decision outcome and each condition's independent
effect. A tool must declare unique-cause, masking, or hybrid MC/DC, represent
short-circuit conditions as true/false/not-evaluated, handle strong coupling, and
report exact rather than rounded 100%. Exclusions need narrow technical rationale
and review.

Production tracing demonstrates two distinct costs: conditional compilation
removes static-off code, while Linux ftrace/static keys and LLVM XRay use dormant
NOP/patch sites for low-cost dynamic activation. Lockless per-CPU buffers and
XRay's flight recorder use fixed binary records, explicit overflow policy, and
deferred formatting.

Android VTS and Vulkan CTS separate shared behavioral contracts from providers.
For HAL comparison, read-only requests can run independently; mutating operations
need one authoritative execution plus trace/replay to prevent duplicated effects.
Pure Simple remains primary; C/Rust are optional baselines, never replacements.

## Primary sources

- NASA/FAA tutorial: https://ntrs.nasa.gov/archive/nasa/casi.ntrs.nasa.gov/20010057789.pdf
- FAA MC/DC variants: https://www.faa.gov/sites/faa.gov/files/aircraft/air_cert/design_approvals/air_software/AR-01-18_MCDC.pdf
- FAA verification tools: https://www.faa.gov/sites/faa.gov/files/aircraft/air_cert/design_approvals/air_software/AR-06-54_VerificationTools.pdf
- FAA short-circuit/object code: https://www.faa.gov/sites/faa.gov/files/aircraft/air_cert/design_approvals/air_software/AR-07-20.pdf
- NASA requirements: https://nodis3.gsfc.nasa.gov/displayDir.cfm?Internal_ID=N_PR_7150_002D_&page_name=Chapter3
- Rust conditional compilation: https://doc.rust-lang.org/reference/conditional-compilation.html
- Linux ftrace: https://docs.kernel.org/trace/ftrace.html
- Linux tracepoints: https://docs.kernel.org/trace/tracepoints.html
- Linux ring buffer: https://docs.kernel.org/trace/ring-buffer-design.html
- LLVM XRay: https://llvm.org/docs/XRay.html
- GCC patchable entries: https://gcc.gnu.org/onlinedocs/gcc/Instrumentation-Options.html
- Android VTS: https://source.android.com/docs/core/tests/vts
- Vulkan CTS: https://github.khronos.org/Vulkan-Site/guide/latest/vulkan_cts.html

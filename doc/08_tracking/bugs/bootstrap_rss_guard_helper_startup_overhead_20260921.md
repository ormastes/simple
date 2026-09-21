# Sampled RSS guard helper startup adds material native compile overhead

Status: OPEN. Observed 2026-09-21 on macOS arm64 while integrating the bootstrap
session helper. Owner area: `scripts/resource/process-tree-rss-watchdog.pl`.

The guard compiles and admits a private helper before every invocation, then
runs authoritative SID observations with each RSS sample. A 3,500-function
`cc -O2 -c` translation-unit benchmark, interleaved three times per mode, gave:

| Mode | Wall seconds | Median |
| --- | --- | --- |
| Plain | 2.033921, 2.024491, 2.016033 | 2.024491 |
| Integrated guard | 2.381332, 2.412733, 2.407496 | 2.407496 |

Regression: **18.92%**, approximately 383 ms per invocation. The last guarded
receipt measured 296,320 KiB peak, 24 RSS samples, 40 SID observations, and
105.025 ms maximum observed sample gap. This benchmark preceded the final
new/inherit admission validation changes and does not measure a Simple bootstrap.

Reproduction: generate 3,500 functions of the form `unsigned fN(unsigned x)`
containing twenty iterations of `(x * 1664525u + 1013904223u) ^ j`; compile
with `cc -O2 -c` directly and through the guard at a 100 ms interval, alternating
modes. Include helper installation in elapsed time.

Required followup: separate installation from steady observation costs, evaluate
reuse of an admitted immutable helper without weakening identity checks, then
measure representative source-matched Simple builds. Preserve decimal 6 GB
emergency maximum and separate decimal 1 GB ordinary-compile acceptance.

Work stopped at the user's explicit push-as-is request. No performance PASS or
strict containment launch approval is implied by this delivery.

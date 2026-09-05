# Resource-bundle memory-performance specification

This executable specification measures real `ResourceBundle` lookup and
multilingual parameter formatting after catalog construction.

Receipts report catalog entry count, catalog UTF-8 bytes, iterations, formatted
output bytes, retained runtime growth, auxiliary growth, array-capacity growth,
and allocation/HWM availability. Zero-valued unsupported counters are reported
as unavailable.

The formatting row intentionally captures the current repeated-`replace`
implementation. It is a baseline for the planned one-pass compiled MessageIR
formatter, not approval of the current algorithm.

Release comparison requires an isolated matched host and functioning allocation
and RSS instrumentation.

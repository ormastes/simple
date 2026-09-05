# Legacy i18n CLI coverage and memory — 2026-08-26

Cycle 1 reproduced a Unicode crash and passed 4/5 at 80% branches (16/20) and
65% lines (70/107). `text.len()` supplied byte length while integer indexing
used scalar ordinals. The scanner now uses `line.chars()` consistently.

The final focused suite passes 5/5 at 95% branches (19/20) and 71% lines
(77/108). It covers log-option cleaning, identifier classes, escapes,
unterminated/ordinary input, deduplication, missing/empty/populated directories,
file filtering, catalog/template writes, and exact Korean preservation. The
remaining empty-key guard is unreachable under the preceding scanner condition;
no 100% claim is made after the three-cycle cap.

The memory-performance smoke passes 1/1 over seven samples and 256 multilingual
messages: input 20,771 bytes, catalog 25,883 bytes, template 27,474 bytes,
p50/p95 48,643/49,836 us, process HWM 66,660 KiB, checksum 375,291. Execution is
interpreter-demoted; allocation, transient, and retained bytes are unavailable.
This does not satisfy the native message rows. The line scanner remains a
compatibility implementation pending delegation to the compiler AST extractor.

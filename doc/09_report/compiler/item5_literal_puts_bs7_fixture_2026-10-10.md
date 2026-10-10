# Item 5 literal puts BS7 fixture (2026-10-10)

Status: focused checker mutation fixture PASS; production qualification pending.

The existing BS7 test used a same-entry C program with the Simple writer.
It now replays the selected literal `puts("hello")` C source and checks the
expected `hello` stdout. Its synthetic Simple runtime delegates printing to
`puts` so this small test can exercise the 1.05 matched-size gate without
changing the gate or asserting a production binary size.

`sh test/01_unit/scripts/runtime_binary_size_startup_cohort_test.shs` passed:
clean cohort, label-only refusal, and matched-link/stdout/sample mutations.
The first edit retained a synthetic `fwrite`/ `fputc` writer and failed
`simple-over-matched-c-105-percent`; the corrected fixture passed on the
second test cycle. The historical Stage4 13,544-byte Simple / 13,264-byte
matched C result remains the only selected numeric diagnostic. No current
release-small binary, NoGC/provider trace, production 30/100 startup/RSS
cohort, architecture matrix, or Phase-7 cutover is proven by this test.

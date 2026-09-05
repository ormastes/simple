# UTF-32 reference and memory evidence — 2026-08-26

The focused reference suite passed 27/27 examples with 100% line coverage
(60/60) and 100% branch coverage (16/16) in its second bounded cycle.

The separate memory lane passed 2/2 examples over 8,190 multilingual scalar
values:

- LE serialization produced 32,760 bytes and round-tripped exactly.
- UTF-32-to-UTF-8 conversion produced 21,294 bytes.

The deployed interpreter returned zero for all registered live, auxiliary, and
array-capacity counters, and does not register process HWM for this execution
profile. Receipts therefore report both allocation count and HWM as
`unavailable`; these zeros are not evidence of zero allocation. Controlled
matched-baseline allocation and RSS qualification remains required.

# UTF-16 reference coverage — 2026-08-26

Owner: `src/lib/common/encoding/utf16.spl`

The second and final required cycle passed 40/40 focused examples with 100%
line coverage (85/85) and 100% branch coverage (23/23). Coverage includes
offset bounds, invalid numeric bytes and code units, malformed surrogate
followers, both endian modes, replacement behavior, and serialization.

The implementation removed one contract-impossible zero-progress branch from
`utf16_decode_all`; `utf16_decode_one` is specified and tested to consume one
or two units for every in-range call.

No post-change latency or memory result is retained. At the measurement point,
the shared host reported load averages 27.45, 35.05, and 26.88 with several
unrelated `simple` processes saturating CPUs. A controlled matched-baseline run
must still report p50/p95, throughput, peak RSS, allocation count/bytes,
temporary bytes, and output-capacity growth before performance closure.

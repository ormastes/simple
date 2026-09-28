# Target 6 bounded archive-member publication (Linux aarch64, 2026-09-29)

Status: focused no-stub Stage-2 native pass with paired member-workload
time/RSS improvement. Production driver cutover and full compile qualification
remain open.

The cold V2/V3 package-index publisher already holds the CAS archive text for
readback. It previously copied each member into a second member-sized `[u8]`,
validated/decoded that array into another text, then hashed the decoded text.
The new path takes the member's exact byte slice once, checks its byte length,
validates UTF-8 with the existing `text_validate_utf8` owner, and hashes the
selected text with `sha256_text`. Archive layout, member digest, manifest,
semantic payload, and `CURRENT` publication gates remain in their prior order.
An 8 MiB pure `byte_at` range-hash trial reduced RSS but increased elapsed
time enough to miss the combined score; it was removed.
`sha256_text` still materializes bytes internally, so this is a measured
peak-memory reduction, not constant-memory hashing of a maximum-size member.

## Focused correctness

The no-stub Stage-2 native build compiled 332 units with zero failures.
`cold_hir_compact_output_index_spec.spl` passed 10/10 scenarios, including
the persisted 542-byte and 131 KiB archives, scoped graph publication,
payload mismatch refusal, malformed semantic payload refusal, and a new
digest-valid invalid-UTF-8 member rejected before `CURRENT` moved. The spec
process's exit code alone is not the verdict; the scenario count is.

## Matched 8 MiB member workload

`test/05_perf/fixtures/target6_bounded_archive_member/workload.spl` runs the
prior copy/validate/hash sequence and the selected slice/validate/hash
sequence in one no-stub 89 KiB binary. Both modes construct the same
8,388,700-byte action member, verify its pinned SHA-256 digest, and print
`pass`. Each mode was warmed once; 30 pairs alternated execution order on the
same host under a 2 GiB virtual-memory limit. Nearest-rank p95 elapsed and
maximum peak RSS are computed from all successful samples.

| Measure | Prior | Selected | Selected / prior |
| --- | ---: | ---: | ---: |
| p95 elapsed | 0.22 s | 0.06 s | 0.273 |
| Median elapsed | 0.21 s | 0.05 s | 0.238 |
| Peak RSS | 99,476 KiB | 33,860 KiB | 0.340 |

The normalized p95 time plus peak RSS ratio is **0.613**, below the `<2`
gate; both measures improve. The workload binary is identical for both
modes, so its size is not a before/after production binary-size result. Raw
samples, source and binary hashes, fixture digest, and run order are in
`target6_bounded_archive_member_pair_2026-09-29.json`.

The cohort measures one archive-member verification operation. It does not
cover full compile/check/bootstrap/MCP/LSP paths, other operating systems,
the 1 GiB member maximum, or a current-source Stage-4 compiler. These remain
Target 6 completion gates.

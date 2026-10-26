# Native bounded process capture loses NUL-separated records

Status: local repair; Windows provider RED/GREEN and production value/tuple
integration passed. End-to-end performance admission failed; POSIX, native Simple
SSpec and Phase3 remain unqualified. Independent of the Phase3 HIR memory limit;
no OOM causality is claimed. See the [repair and evidence report](../../09_report/native_process_capture_nul_length_2026-10-11.md).

The retained Phase3 chunk13 log contains:
`workarounds: refresh failed: truncated workaround Git status output`.
Cache artifacts also show HIR progress later in that run, so this warning is not
evidence that execution stopped before parsing or that workaround scanning caused
the memory-limit termination.

## Cause

`src/app/bug/workaround_store.spl:194` requests Git porcelain status with `-z`.
`workaround_status_paths` correctly requires terminal NUL framing and handles
rename destination/source pairs. `workaround_git` uses a 30-second, 16-MiB bounded
process call through `std.nogc_async_mut.sosix.workaround_host`.

That facade aliases `std.nogc_sync_mut.io.process_ops.process_run_bounded`.
On native Windows, `runtime_process.c:583` routes to `win_process_run_capture`.
The capture retains explicit lengths but passes only pointers to
`process_timeout_result` at line 557. That result constructor at line 172 creates
stdout text with `strlen(out)`, dropping the first NUL and everything after it.
Stderr and timeout-marker construction have the same length-loss issue. A complete
Git response below the output limit can therefore appear truncated to its caller.

The error propagates before `workaround_prepare_locked`, so that failing refresh
does not reach source scanning or canonical bug-database loading. The coordinator
prints the warning and proceeds.

## Repair boundary and verification

Preserve captured byte counts at the canonical process provider, or use an
existing owned-byte capture facade with equivalent deadline, output-bound, exit,
and cleanup behavior. Keep Git's NUL framing and the parser's fail-closed check.
Do not trim the output, accept a missing final NUL, or silently drop rename fields.
The local repair now carries explicit byte lengths through the C constructor and
adds POSIX captured-length getters. Full evidence and admission limits are in the
linked report; the earlier source review alone did not modify the provider.

Required executable cases: empty stdout; multiple NUL-separated records; embedded
NUL on both streams; Git rename/copy source and destination; paths containing spaces;
exact-bound and over-bound output; timeout with NUL-bearing stderr; and unchanged
text-only consumers. Verify length and every byte, not only a decoded prefix.
Run `test/02_integration/app/bug_workaround_store_spec.spl` through a qualified
native process-capture path. The existing in-memory parser fixture alone does not
exercise this transport defect.

## Independent allocation reduction

`workaround_index.spl:workaround_lexical_state` constructs up to three substrings
per scanned source byte. `parse_workaround_source` now returns an empty result
after path validation when the exact contiguous `@workaround` prefix is absent,
avoiding line splitting and lexical slices for ordinary source. All link creation
and marker errors require that prefix; files containing it still use the original
lexer and validator.

Regression spec: `test/01_unit/app/workaround_source_no_marker_spec.spl`, covering
large ordinary text, fragmented/case-different prefixes, invalid paths, quoted and
multiline examples, block comments, real annotations, and malformed markers.
The SSpec remains UNRUN. This change does not repair the capture defect and is
not claimed to fix chunk13 HIR memory.

### Phase1 diagnostic execution (2026-10-11)

The user-authorized Rust seed diagnostic imported immutable captures of the real
`workaround_index.spl`, with identical standalone boolean checks derived from all
four authored cases. Baseline and candidate each passed all four groups and the
final success sentinel, with seed/logger/receipt exit 0. Inputs retained their
pinned hashes and both Windows Job process trees closed quiescently.

| Lane | Wall seconds | Peak RSS KiB | Peak Job commit KiB |
|---|---:|---:|---:|
| Baseline | 2.4070927 | 51,220 | 71,292 |
| Candidate | 3.1841605 | 38,044 | 59,124 |

Each lane ran once under 120 seconds, a 1 GiB process-tree RSS cap, and a 16 MiB
log cap. These are whole diagnostic invocation observations, not allocation
counts or a statistically supported performance comparison. Candidate elapsed
time was higher in this pair; no throughput improvement or 0.1-second target is
claimed. Pure-Simple qualification and the original SSpec remain UNRUN.

Evidence directory: `build/native_probe/workaround-no-marker-phase1-20261011-v2/`;
each lane retains `RESULT.json`, `phase1.rss.env`, and `compile/retained.log`.
Request SHA-256: `cb2a1720f9f240962217c2cc0dcb4c47cbb0b67b87a90c82af44206d47b10ad4`.
Seed SHA-256: `6b133a15211e2ffb7c8c289a151400dc9a173e70b72e1c9f2feb6589e5dd0e0e`.
The first harness attempt is preserved separately at
`build/native_probe/workaround-no-marker-phase1-20261011/baseline/`: it exited 1
before the cases because bare `assert` was undefined. Its candidate never ran.
The corrected harness returns false at each failed condition and makes `main`
return 1 with a case failure label; only all four true results print success.
This completed the second bounded diagnostic cycle; no successful check reran.

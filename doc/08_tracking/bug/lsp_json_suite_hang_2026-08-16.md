# lsp_json "suite hang" — no hanging spec; directory-run throughput on seed binary (2026-08-16)

## Symptom
A run of the lsp_json test suite appeared to hang and was killed after 15 min.

## Binary identity
- `readlink -f bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`
- `bin/simple --version` prints the Rust **seed** warning banner — tests ran on the seed, not a self-hosted binary.

## Evidence (all runs 2026-08-16, this tree)
Every lsp_json-related spec passes individually well inside `timeout 300`:

| spec | Results | RC |
|---|---|---|
| `test/01_unit/app/lsp_json_spec.spl` | 13 total, 13 passed | 0 |
| `test/unit/app/lsp_json_spec.spl` (mirror) | 13 total, 13 passed | 0 |
| `test/01_unit/app/lsp_handlers_spec.spl` | 8 total, 8 passed | 0 |
| `test/01_unit/app/query_symbols_spec.spl` | 3 total, 3 passed | 0 |
| `test/01_unit/app/mcp_t32/mcp_t32_json_spec.spl` | 8 total, 8 passed | 0 |
| `test/03_system/gui/editor_lsp_transport_spec.spl` | 48 total, 48 passed | 0 |

No blocking read / IPC / infinite loop was reproducible in any lsp_json spec.

## Root cause of the apparent hang
The "suite" run was a directory-level run (`bin/simple test test/01_unit/app`,
which contains `lsp_json_spec.spl`). Two compounding causes:

1. **Throughput, not a hang.** The directory holds **1308 spec files**; a 570 s
   run completed only 83 of them (~7 s/spec average incl. per-spec setup on the
   seed) → full-directory ETA ≈ 2.5 h. A 15-min kill lands mid-run with no
   output for long stretches, indistinguishable from a hang.
2. **External CPU guard kills it first anyway.** With default settings the run
   dies at ~64 s: `TIMEOUT: killed by kill_simple_monitor (cpu=99.9%
   age=64s>=60s)`. Raise with `SIMPLE_TIMEOUT_SECONDS=<secs>`; the in-process
   watchdog then kills at that wall clock (`[watchdog] wall-clock timeout`),
   crash log e.g. `.simple/logs/crash_955153.log`.

## Separate real finding (pre-existing, not a hang)
`test/01_unit/app/build/build_targets_spec.spl`: **45 total, 38 passed,
7 failed, 38348 ms** — the slowest spec observed and it carries 7 real
assertion failures. Deserves its own triage; not touched here.

## Unblock / recommendation
- Run lsp_json specs as single files; they are green in seconds.
- Directory runs of `test/01_unit/app` on the seed are impractical (~2.5 h);
  either deploy the self-hosted binary or run with
  `SIMPLE_TIMEOUT_SECONDS` sized to the real ETA.
- Related prior record: `deployed_seed_test_runner_init_hang_2026-07-17.md`.

## RESOLVED (2026-08-17)
Re-verified in this tree (`bin/simple` = seed at
`bin/release/x86_64-unknown-linux-gnu/simple`, concurrent bootstrap load):
`timeout 280 bin/simple test test/01_unit/app/lsp_json_spec.spl` → **13 total,
13 passed, 0 failed, RC=0**. There is no hanging spec and no code defect in
lsp_json; the "hang" was directory-run throughput on the seed (1308 specs,
~2.5 h ETA) plus the external CPU guard, exactly as diagnosed above. Note:
under heavy concurrent load even the single spec can exceed 120 s (one run was
killed at `timeout 120` before passing at 280 s) — always size `timeout`
generously on a loaded machine. Resolution = run specs as single files or with
`SIMPLE_TIMEOUT_SECONDS` sized to the real ETA; no test was skipped or changed.
The separate `build_targets_spec.spl` 7-failure finding remains open and is not
covered by this resolution.

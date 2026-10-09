# Stage 2 SCV cold init: `str_contains`/`str_replace_all` per-byte slice loops and a 180 s probe that carried the whole cold init

**Status:** per-file canonicalization FIXED (`src/lib/common/string_core.spl`),
gate restructured (`scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`);
snapshot materialization cost remains OPEN (below).
**Host:** Windows 11, x86_64-pc-windows-msvc, Git Bash, pure-Simple stage-2
`simple.exe` (frozen candidate sha `9309c024…`), worktree 45,079 tracked
`.spl`/`simple.sdn` under src+test, 295 MB.

## Symptoms

1. Any native-build in a fresh checkout fails in ~45 s with
   `SCV-E-ADMISSION: compile-event-journal-missing (… rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)`.
2. The stage-2 sanity gate's `p2_add` probe exports the cold-init opt-in
   itself and times out at 180 s (exit 124) with no compiler output, so stage 2
   is never admitted and no phase-2 test runs.
3. A hello-world native-build with cold init on the frozen stage 2 ran
   981 s (cold init ~890 s), single-threaded, printing nothing.

## Root cause (measured, seed-built bench calling the production functions)

`compile_source_inventory_whole_text_eligible_v1` runs 23 `content.contains(needle)`
scans per source; on the native lanes a `contains` on a typed `text` receiver
resolves to `std.common.string_core.str_contains` -> `str_index_of`, whose loop
was `s[i:i + sublen] == sub` — one heap substring allocated, registered and
reclaimed PER INPUT BYTE. `str_replace_all` (behind `text.replace`, used by the
canonical/facet passes) had the same shape. Measured on one 3.5 KB source:

| op | before | after |
|---|---|---|
| `eligible_v1(sample)` x50 | 3.9 s (~77 ms/call) | 0.5 s (~0.5 ms/call) |
| 300 files (2.7 MB): eligible / canonical / rows | 68.2 s / 33.3 s / 22.8 s | 0.32 s / 0.62 s / 0.36 s |
| `rt_string_contains` x200 (raw worker) | 4 ms | 4 ms |

The frozen stage 2 shows the slow path only when `SIMPLE_LIB` does not point at
a checkout (`check`/spec children, ad-hoc builds: 20–100 ms/file); with
`SIMPLE_LIB=<root>/src` the same binary resolves the method to the native
worker and runs at ~4.4 ms/file — which is why the gate probe (which sets
`SIMPLE_LIB`) still exceeded 180 s: 45k x 4.4 ms + `git ls-files` 12 s +
publish 13 s + snapshot materialization ~3.6 min.

## Fix

- `str_index_of` and `str_replace_all` jump between matches with the native
  byte search `text.index_of(sub, start)` (`rt_text_find`), the idiom
  `str_split` already used. Results unchanged; `string_core_{ops,basic,advanced}_coverage_spec` 639/639 pass.
- The gate runs the one-time cold init as its own `scv_prime` step (own log,
  receipt, `COMPILER_SCV_PRIME_TIMEOUT_SECONDS`, default 1800 s, own cache
  dir) and fails closed when no `build/scv/source-inventory/CURRENT` exists
  afterwards; `p2_add` and every later probe admit warm under the unchanged
  180 s bound. No admission check was weakened: the inventory is still the
  compiler's own fail-closed publication.

## Measured before/after (stage 2 rebuilt with the Rust seed, 14 threads, same env)

| | frozen stage 2 | stage 2 + fix |
|---|---|---|
| 300-file git repo, no `SIMPLE_LIB`: inventory refresh | 29 s | 3.4 s |
| full worktree (45,079 files), `SIMPLE_LIB` set: per-file loop | 200 s | 145 s |
| full worktree: inventory publish (CURRENT) | 212 s after start | 158 s after start |
| full worktree: snapshot published (end of cold init) | 436 s after start | 511 s after start (snapshot phase 5.8 min vs 3.6 min; two bench jobs were reading the same tree during it) |
| bench, 45,079 files, no `SIMPLE_LIB`: per-file loop | >5 h (0.57 s/file extrapolated from 2,000 files in 1,135 s) | 160 s |

Published artifacts are byte-identical between the two binaries: inventory
`887d0bd6d8ce…` (45,080 entries), CURRENT cursor, untracked membership record.

## Still open

- The remaining per-file loop is ~3.3 ms/file of file open+read through
  `rt_file_read_text_at_checked` (Windows; Python reads the same files at
  0.9 ms/file) plus ~1 ms canonicalization — single-threaded.
- Snapshot materialization after the inventory (`scv_compile_snapshot_acquire_v1`)
  costs ~3.6 min on this tree: per source it reads+hashes, writes a chunk
  blob with read-back verification, writes the snapshot copy with read-back
  verification, and re-reads the source for drift. The chunk publication is
  pinned by `test/04_smoke/native_scv_chunk_publication.spl`, so it was not
  changed here; cutting it needs an owner decision.

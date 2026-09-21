# macOS compiler peak RSS exceeds the 1 GB budget

Scope: native `aarch64-apple-darwin`. Status: OPEN; corrections improved the
broad rebuild but the final memory gate failed. No other host is covered.

## Requirement and baseline

The compiler process must peak below 1,000,000,000 bytes RSS, including
canonical Stage 3 at jobs=8. A small fixture does not certify the full closure.
At source `0fc5c8ba12b`, canonical jobs=1 Stage 3 reached all 841 modules.
RSS was 803,184 KiB at 1:41, 7,548,144 KiB at 2:32 during export-origin
revisits, and 3.3–3.7 GB during the backend. The run was stopped at about
14 minutes on the user's request to use jobs=8. The memory requirement failed.

## Ownership correction

Streaming export-origin resolution now scopes its first and fixpoint work
per surface. Six origin-index projections and returned error text survive;
lookup objects, import-walk temporaries, and trace strings are reclaimed.
Export precedence, ambiguity checks, and pass order remain unchanged. Existing
unscoped callers retain their behavior. HIR promotion also discards importer-
qualified glob misses. Registry-wide caches remain retained. Pre-scope empty
cache containers remain a retention limitation; eviction alone is not proof
of meeting the memory budget.

## Focused jobs=8 startup failure

At `5bb25555556`, rebuilt Stage 2 compiling the explicit-export three-file
fixture with `--threads 8`, a fresh cache, and
`SIMPLE_SCV_INVENTORY_COLD_INIT=1` emitted no compiler output. It was stopped
at 95.84 s (94.85 s user). `/usr/bin/time -l` reported maximum RSS
3,812,573,184 bytes and 1,908,981,055,619 instructions. No executable existed.
The earlier 8.041 s fixture used the direct route and is not a matching
jobs=8 baseline.

A diagnostic with the same flags plus `SIMPLE_BOOTSTRAP_DIAG=1` stopped at
25.5 s with peak sampled RSS 962,224 KiB. macOS `sample` at eight seconds
places the work in `lib__common__string_core__str_split` and native equality.
There was no export-origin/compiler progress. `--threads 8` selects the
process route, whose SCV inventory cold-init precedes lowering. The git
listing contains 3,597,989 bytes / 60,731 paths. The single-character split
loop allocated one temporary text slice per candidate byte. This is a separate
startup allocation problem; it does not establish an export-scope regression.

The final correction scans ASCII separators with `byte_at`, allocating only
output field slices. ASCII cannot match a UTF-8 continuation byte, so field
boundaries remain valid. Empty/trailing fields are preserved; other separator
paths keep their behavior.

## Final measurement

Evidence: `build/native_probe/memory-diagnostic/sample.txt`, `rss.tsv`, and
the empty `compiler.log`. The watchdog terminated the diagnostic after its
sample. New unit assertions cover UTF-8 fields, empty boundaries, multi-byte
separators, delayed aliases, ambiguity cleanup, and nested-scope rejection;
they are authored, not claimed as executed by compiler-only Stage 2.

The final combined Stage 2 jobs=8 admission passed in 119.11 s with maximum
RSS 1,320,648,704 bytes. The comparable earlier rebuild took 647.73 s and
peaked at 3,470,360,576 bytes, so the ASCII split correction improved time
5.4x and reduced peak RSS 62%, but still missed the 1 GB limit.

The final fresh-cache fixture again exceeded the limit before emitting
compiler output. It was stopped at 48.30 s; `/usr/bin/time -l` reported
4,580,589,568 bytes maximum RSS and 835,533,027,401 instructions. No artifact
was produced. The three-cycle cap is exhausted, so canonical Stage 3 was not
started. The memory bug and TODO remain open as release blockers.

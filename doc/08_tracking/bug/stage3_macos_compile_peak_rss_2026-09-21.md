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

## Stage 3 retained-diagnostic correction, 2026-09-21

Stable evidence from the later jobs=8 run is
`build/evidence/macos-bootstrap-20260921/stage3-native-build.log`, SHA-256
`11ab3d606b1d0ed508cf2c28b11c8d2e368c4b3983835eda9c7a6427d92c5a1c`.
The run reached HIR module 618 of 847 before SIGBUS and peaked at
15,971,434,496 bytes RSS. Of 92,363 log lines / 29,266,762 bytes, 70,917 lines
and 27,018,948 bytes (92.3%) are the same
`[hir-reexport-chase-unresolved]` receipt. Its owner rendered a long
interpolated message unconditionally for every routine failed facade chase,
even though the later canonical unresolved-name/type diagnostic remains.

The detailed attribution is now rendered only when
`SIMPLE_BOOTSTRAP_DIAG=1`, matching the other re-export trace receipts. The
environment value is resolved once when each `HirLowering` context is created;
failed chases read the cached boolean, avoiding both per-miss environment text
allocation and message interpolation. The policy is isolated in
`compiler.hir.reexport_diagnostic_policy` so the default and enabled behavior
can be exercised without a full bootstrap. A unit spec verifies constructor
behavior for unset, `0`, and `1`, and invokes the actual failed-chase reporter.
A reciprocal resource spec compares three parent renderer plus injectable-sink
trials with three fixed production-caller trials at 20,000 misses, using median
elapsed, live-object, and live-heap measurements. It also runs three enabled
production trials of eight calls, including stderr emission, under a one-second
median timing bound. The incoming diagnostic environment is restored before
profiles or assertions run.

Verification on the admitted Stage 2 producer:

- The policy module compiled to SMF in 4.41 s with 180,027,392 bytes maximum
  RSS.
- The unit spec and all 26 dependencies parsed; lowering reached the existing
  `std.spec` dependency defects (`process_run`, `read_file_text`, and
  `time_now_unix_micros` unresolved), so execution is pending a full CLI that
  can load this source revision.
- The prior full CLI test runner fails earlier while parsing the existing
  `src/lib/nogc_sync_mut/io/process_ops.spl`; it cannot execute the specs.
- The direct-env runtime guard passes.

The 28 MiB retained output establishes the dominant logged allocation path,
but does not by itself account byte-for-byte for the 15.97 GB RSS peak. A
fresh Stage 3 run is still required to measure the reduction and to decide
whether the terminal SIGBUS has an additional HIR cache-lifetime owner. The
bug remains open and the sub-1 GB requirement remains unmet.

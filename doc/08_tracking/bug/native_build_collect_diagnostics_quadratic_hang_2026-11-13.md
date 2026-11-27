# native-build diagnostic collection hangs O(n²): index-of-from-offset rescans the whole prefix per line

- Status: fix landed 2026-11-13 (PR pending reference in row)
- Found: 2026-11-13
- Component: `src/app/cli/native_build_main.spl`
  (`native_build_collect_diagnostics`, stderr-truncation path of
  `eprint_bounded`)
- Binary: stage2-admitted pure-Simple compiler (pinned `5e217d7fd0e`), macOS
  aarch64 24 GiB

## Symptom

A stage-3 resume lane completed the full 1651-module AOT
(`aot:bootstrap_fixed:done`, ~42 min) and then hung: 7+ hours at ~90% CPU
with no log growth, killed manually. `sample(1)` of the hung process:

```
2473 start
  2472 app__cli__native_build_main__native_build_collect_diagnostics + 88
    1533 rt_text_find -> text_cp_len_memo / text_cp_to_byte
     553 rt_text_find -> text_cp_to_byte
     381 rt_text_find -> text_cp_len_bytes
```

## Root cause

`native_build_collect_diagnostics` scanned lines with
`output.index_of("\n", line_start)`. `text.index_of` with a byte start
offset converts the offset through codepoint space on EVERY call
(`rt_text_find` → `text_cp_len_bytes`/`text_cp_to_byte` prefix walks — the
memoized cp-count cache from PR #8554 does not help; the per-call prefix
conversion is still O(offset)). For a stream with L lines the loop is
Σ O(line_start) = **O(n²)** over the whole stream. The per-line needle
matching (`native_build_range_contains`) was byte-wise and fine; the newline
scan was the trap.

Trigger conditions: any native-build whose captured output exceeds
`OUTPUT_LIMIT` (12000 bytes) routes through `eprint_bounded` →
`native_build_collect_diagnostics`. The 2026-11-13 stage-3 run had a ~121 MiB
`[BOOTSTRAP-PHASE]` trace stream, so the "collect every diagnostic line
before truncating" safety pass never finished.

## Fix

`native_build_collect_diagnostics` now does ONE `str_split(output, "\n")`
pass (single O(n) byte walk, the idiom `string_core.spl` already documents)
and tests each small line with the existing byte-wise
`native_build_range_is_diagnostic(line, 0, line.byte_len())`. Semantics
unchanged: same lines kept, same order, empty tail line never diagnostic.

## Why a runtime fix is not the (whole) answer

The deeper defect — `rt_text_find` prefix conversion making
`index_of(needle, offset)` O(offset) per call — lives in the Rust runtime
collections (`text_cp_len_memo`/`text_cp_to_byte`) and its C twin. It should
be fixed there too (incremental cp/byte cursor or byte-first search for the
ASCII case), but any runtime change only reaches deployed binaries through a
rebuilt compiler. The source fix here removes the only in-repo loop that
calls `index_of` with a growing offset over a giant stream, so binaries
built from this source no longer hit the hang regardless of runtime.

## Evidence

- Sample of hung pid: `/tmp/stage3-hang.sample` (call graph above).
- Lane log frozen after `aot:bootstrap_fixed:done`;
  `stage3-native-build.log` = 121 MiB, last write ~7 h before kill.

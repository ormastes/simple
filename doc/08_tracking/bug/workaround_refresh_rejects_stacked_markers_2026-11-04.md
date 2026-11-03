# Workaround refresh rejects two stacked `@workaround` markers

- id: workaround_refresh_rejects_stacked_markers_2026-11-04
- status: open
- priority: P3
- found: 2026-11-04, phase-3 F3 lane (stage3 `s3_fable16` native-build of the test runner)

## Symptom

Every native-build over `src/lib` prints, non-fatally:

```
workarounds: refresh failed: build/scv/snapshots/<rev>/src/lib/common/serialization/__init__.spl:407: workaround must immediately precede the affected block
```

## Cause

`src/lib/common/serialization/__init__.spl:407-408` carries two consecutive
markers on `pub fn escape_string`:

```
# @workaround bug=methods_mir_2026-10-31 reason=...
# @workaround bug=rti007_any_return_rows_2026-11-01 reason=...
pub fn escape_string(value: text) -> text:
```

The refresh scanner requires the line after a marker to be code, so the first
of two stacked markers is rejected. The whole refresh then aborts, so no
workaround inventory is updated for the run.

## Expected

Either the scanner accepts a run of adjacent `@workaround` lines as all
applying to the next block, or the lint rejects stacking at authoring time.
A single bad marker should not abort the refresh of every other marker.

## Repro

`bin/simple native-build --entry <any> --source src/lib ...` and read stderr.

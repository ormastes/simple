# Pure-Simple COFF linker: archive long-name table exhausted >100 GB

- **Status:** fixed by the PR that adds this record
- **Component:** `src/compiler/70.backend/linker/archive_parser.spl` (`ar_parse`)
- **Found:** 2026-10-27, Windows x86_64, linking the stage2 hello-world objects
  with the internal COFF engine (`SIMPLE_LINKER=internal` path, exercised
  through a native-built probe)

## Symptom

A probe (`h_pcoff.exe`) that calls `coff_link_default_libraries` /
`coff_link_amd64_retained_image_policy_full` on the 43 hello-world objects plus
the MSVC/SDK import libraries grew to **107-138 GB private memory** before any
output, exhausted host commit, and took down unrelated builds (host reboot).
Narrowed under an 8 GB cap: one input object plus `msvcrt.lib` alone is enough.

## Root cause

`ar_parse` built the `//` extended-name table one character at a time
(`ntbl = ntbl + ar_byte_to_char(...)`). `msvcrt.lib` (14.44.35207) has a
125,063-byte name table, so the build is quadratic (~7.8 GB of intermediate
strings per parse) and, because the module is `@no_gc`, none of it is
released. `ar_parse` runs several times per link (member scan, import scan,
each closure pass), so the total runs away.

A second defect in the same code: MSVC terminates long-name entries with NUL,
not GNU `/\n`. NUL was mapped to `?`, so every MSVC long name ran on into the
following entries (and each lookup concatenated that whole run).

## Fix

- `ar_name_table_text` builds the table once from a sanitized byte copy
  (NUL becomes `\n`, other non-printables `?`, so byte offsets stay character
  offsets) with a single `bytes_to_text`.
- `ar_lookup_extended_name` finds the terminator and takes one slice.

Spec: `test/01_unit/compiler/backend/linker/archive_parser_long_names_spec.spl`
(red before the fix: `expected second_long_name.obj? to equal second_long_name.obj`).

## Repro (do not run uncapped)

Any `ar_parse` of `msvcrt.lib` from the pure-Simple linker. Always run linker
probes under a process-tree memory cap (8 GB), e.g.
`C:/dev/wt-perf/build/probe/capwatch.ps1 -RootPid <pid> -CapGB 8`.

## Remaining (not fixed here)

After this fix a full hello-world COFF link still needs ~1.8 GB per
`_coff_prepare_link` call (every member of every library is materialized and
parsed per call; `@no_gc` keeps it all), so the default-library loop plus the
final link exceeds an 8 GB cap. Tracked in
`pure_coff_linker_closure_parses_every_member_2026-10-27.md`.

# Tracked checkout LOC — 2026-11-24

The requested language inventory contains **25,736,032 code/data lines** in
**84,587 files**, or **29,806,779 physical lines** including comments and blanks.
This includes submodules and vendored code. It is a size measurement, not
evidence of implementation completeness, test coverage, or runtime readiness.

## Measured totals

| Language | Files | Code/data lines | Comments | Blank | Physical lines |
|---|---:|---:|---:|---:|---:|
| Rust (`.rs`) | 30,876 | 19,072,083 | 1,318,521 | 677,443 | 21,068,047 |
| Simple (`.spl`) | 46,513 | 5,529,345 | 891,795 | 885,009 | 7,306,149 |
| C and headers (`.c`, `.h`) | 1,808 | 517,927 | 95,812 | 73,309 | 687,048 |
| SHS (`.shs`) | 3,520 | 473,234 | 70,305 | 39,387 | 582,926 |
| SDN (`.sdn`) | 1,653 | 109,203 | 3,370 | 5,652 | 118,225 |
| Python (`.py`) | 217 | 34,240 | 5,587 | 4,557 | 44,384 |
| **Total** | **84,587** | **25,736,032** | **2,385,390** | **1,685,357** | **29,806,779** |

Code/data lines exclude tool-recognized comment lines and blank lines.
Commented-out code counts as comments when recognized by the language rules;
this is lexical counting, not a semantic dead-code analysis. SDN contributes
data lines rather than executable code. No source comments were deleted.

## Scope

- Enumerated tracked index paths and recursively enumerated populated Git
  submodules; read the actual working files, including local modifications.
- Selected exactly `.spl`, `.shs`, `.sdn`, `.c`, `.h`, `.rs`, and `.py`.
  This is not an all-extension or Markdown/documentation total.
- Included vendored/third-party files, tests, fixtures, and tracked data.
  Separate paths containing identical content count separately.
- Excluded untracked build outputs, caches, and untracked source files.
- Included 36 empty files in the file totals; they contribute zero lines.

The actual Git submodules included were `.spipe/spipe` (96 selected files)
and `examples/08_gpu/simple_cuda_example` (60 selected Simple files;
5,890 code, 1,154 comment, and 1,019 blank lines). CUDA was initialized at
its pinned revision `7126ab5d530fb30d712998b0086193483783a5af` for this count.
Other configured example paths tracked as ordinary files in this checkout
were counted through the main index, not added a second time.

One tracked transient result file was absent and could not be counted:
`test/02_integration/app/.simple_result_1784360018122401_scv_tree_file_link_safety_spec.spl`.

## Tool and counting rules

Used **cloc 2.12**, with the official native Windows executable for the main
count. The initial Git-Perl invocation was slow and was stopped; its incomplete
output was not used. The completed CUDA count used the same cloc version.

The main invocation used an explicit file list and these options:

```text
--list-file=files.txt
--read-lang-def=languages.def
--force-lang=Bourne Shell,shs
--force-lang=C,h
--skip-uniqueness
--csv
```

Custom Simple and SDN definitions recognize full-line comments matching
`^\s*#`. SHS uses the built-in Bourne Shell counter; C, Rust, and Python use
the built-in language counters. These are lexical tool rules, not a complete
parser-based classification of every comment or string form.

The completed main cloc count excluded one fixture under `.config` and two
Unicode-named fixtures. Those three files were counted separately from
byte-identical copies at ASCII paths, adding 16 code/data, 3 comment, and
2 blank lines. Their original paths were:

- `test/03_system/app/devhub/feature/fixtures/poison_home/.config/devhub/email.sdn`
- `test/fixtures/compiled_tool_protocol/protocol café.spl`
- `test/fixtures/lsp_utf8/données/módulo.spl`

An independent binary read counted newlines plus any final unterminated line
across all selected files. Its **29,806,779** total exactly matches the final
cloc code/data + comment + blank total. It reported no read errors.

## Provenance and retained evidence

This is a measurement of the working checkout at `C:/dev/simple`, not an
immutable release or a claim that all files match a Git revision. The main
checkout HEAD recorded at reporting was
`f23cf6fa17bfe7205783ab7f3b55d85603ae96e6`; other sessions had local changes.
The source was not frozen during counting. Counts were finalized on
2026-11-24 at 07:03:47 UTC.

The portable [SDN summary](project_loc_2026-11-24.sdn) records the final totals.
Full local evidence is retained under `build/verify/loc-report/`:

- `coverage.json`, `files.txt`, `cuda-files.txt`: inventory and missing-file scope.
- `cloc.csv`, `cuda-cloc.csv`, `hidden-cloc.csv`, `unicode-cloc.csv`: completed counters.
- `counted.txt`, `ignored.txt`, `cuda-counted.txt`, `cuda-ignored.txt`: tool coverage.
- `languages.def`: custom language rules.
- `physical.json`: independent totals by extension, with no read errors.

The [August project statistics](project_statistics.md#historical-inventory--2026-08-13)
exclude vendored/generated content and use a different inventory definition.
Those figures remain historical and must not be presented as a direct growth
comparison or as current coverage/test evidence.

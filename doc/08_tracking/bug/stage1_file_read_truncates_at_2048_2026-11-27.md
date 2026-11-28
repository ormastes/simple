# Stage1-built stage2 truncates std.io_runtime file_read near 2048 bytes

Status: REFUTED 2026-11-27. There is no read truncation. Root cause and
evidence are in `stage2_test_runner_libunit_project_name_missing_2026-11-27.md`:
the Rust seed rebinds text `.slice(a, b)` to `compiler.frontend.core.types.str_slice`
(code-point `s[a:b]`), and two em dashes ahead of `project:` shifted the cut by
4 bytes. Measured on the failing Stage 2 binary: under `gdb`, its own
`file_read` returns all 2489 bytes of a pre-reorder copy, and its strip
function then returns 344 bytes starting `ect:` instead of 348 starting
`project:`. "Name beyond byte 2048" was a
coincidence of that one file. The manifest reorder below does avoid the failure,
but only because strip returns the source unsliced when line 1 is content. The
original text follows unchanged.

Workaround REMOVED 2026-11-28: the manifest reorder (`a17add1a2c0`) is reverted
and the file is back to the essay-first layout (`project.name` at byte ~2150),
and the `str_slice` source workaround in `src/compiler/10.frontend/core/types.spl`
is reverted to `s[start:end_idx]`. Evidence that removal is safe: the seed fix
(`af6ed58435c`, PR #12183) is an ancestor of bootstrap pin `f3cf72db4299`, whose
rebuilt Stage 2 ran `test_runner_build` with the exact pre-fix failure step now
passing — `library-unit-dynlib] units=4 reused=0 built=4` and
`phase=link state=succeeded` for `simple_test_runner`
(`build/bootstrap/pinned-src/pinned-f3cf72db4299/.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/test_runner_build.log`);
plus the seed fix's `numeric_receiver_resolution_tests` cargo unit tests (7/7).

Addendum 2026-11-27 (seed fix): the resolver defect itself is now fixed in the
Rust seed. `resolve_name_variants`
(`src/compiler_rust/compiler/src/pipeline/native_project/imports.rs`) gates both
lowercase-joined lookups (`str_slice`, `strslice`) with
`is_builtin_receiver_type`, so a builtin-receiver method call (`str.slice`,
`str.len`, ...) can no longer rebind to a same-spelled user free function; it
falls through to the builtin lowering (`rt_slice_text_bytes`, ...), which is the
behavior every small probe already had. Regression coverage:
`numeric_receiver_resolution_tests` in the same file. End-to-end validation
landed 2026-11-28: the rebuilt Stage 2 at pin `f3cf72db4299` (which contains the
seed fix) ran `test_runner_build` with the library-unit packaging step green
(log cited above), so both workarounds were removed — see "Workaround REMOVED"
above.

## Symptom

Stage 2 compiler-test matrix `test_runner_build` row (lanes v7c pin
06ba866385d5 and v7d pin 3dd00937c329, 2026-11-26/27) fails at dyn-lib
packaging:

```
error: focused native-build: library-unit dyn-lib packaging failed:
  src/compiler/00.common/simple.sdn: project.name is missing
```

The manifest is well-formed and `project.name` parses correctly with any
freshly compiled parser (see probes below).

## Evidence

- Reproduced outside the harness with the lane's stage2 binary:
  `native-build --mode dynload --entry-closure --source src --entry
  src/app/test_runner_new/main.spl` from the pinned root fails identically
  after a clean 321/321 link.
- The manifest-closure walk parses `src/app/simple.sdn` (name at byte 43) and
  `src/compiler/simple.sdn` (name at byte 277) fine and fails ONLY on
  `src/compiler/00.common/simple.sdn`, whose `name:` sits at byte 2150 —
  the only manifest in the closure with `project.name` beyond byte 2048.
- Probes compiled BY the failing stage2 binary read the full 2528-byte file
  via `std.io_runtime.file_read` and parse it correctly
  (`len=2528 NAME=simple-compiler-common`), both from an embedded string and
  from disk. Fresh code is correct; the defect exists only in the
  stage1-compiled copy inside the stage2 binary.
- Lane v7d carried the reinstated `val trimmed: text` annotation
  (mir_text_bytes_unresolved_inferred_trim_receiver_2026-10-23) and still
  failed identically, ruling out the inferred-trim-receiver miscompile as
  the cause of THIS failure.

Conclusion: the stage1 compiler miscompiles the `file_read` /
FileTextSession read loop (or its rt marshalling) so that reads truncate at
approximately 2048 bytes. Content past the boundary is silently lost; for
00.common's manifest the loss removes the whole `project:` block, and the
comment-only remainder parses to Null, surfacing as "project.name is
missing".

## Workaround (this commit)

`src/compiler/00.common/simple.sdn` reordered: the `project:` block now
leads the file (name at byte 9) and the explanatory essay moved below it.
No semantic change. REMOVE this reordering note when the compiler defect is
fixed and a lane proves a >2048-byte manifest parses in the stage2 binary.

## Proper fix (open)

Find the stage1 codegen defect in the FileTextSession read loop
(`src/lib/nogc_sync_mut/io/file_text_session.spl` read chunking:
capacity/requested arithmetic around 256/8192) or its extern marshalling.
A regression spec needs a stage2-binary-executed read of a >2048-byte file
via std.io_runtime.file_read with content assertions past byte 2048.

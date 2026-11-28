# Stage 2 test-runner build: `00.common/simple.sdn: project.name is missing` (2026-11-27)

**Status:** fix-implemented, workarounds removed. The Rust seed resolver fix (2026-11-27, "Seed fix" under Open) is confirmed by a rebuilt Stage 2 (2026-11-28: pin `f3cf72db4299` contains `af6ed58435c`; its `test_runner_build` run passed the library-unit packaging step that failed pre-fix — evidence under Workaround below), so both workarounds (the `str_slice` body below and the manifest reorder `a17add1a2c0`) were removed. Not formally closed: no reproducer/prevention spec pair is attached. Owner: bootstrap lane.

## Root cause (2026-11-27, proven with the exact Stage 2 producer)

Not a read truncation and not the inferred-`trim` receiver. The Stage 2 binary is produced by the **Rust seed** (`native-build --backend llvm`, `stage2-command.transcript`). The seed resolves a text method call `x.slice(a, b)` (MIR name `str.slice`) through `resolve_name_variants` (`src/compiler_rust/compiler/src/pipeline/native_project/imports.rs`, the `lower_joined = format!("{}_{}", type_part.to_lowercase(), method_part)` lookups at lines 216 and 238). That spelling is `str_slice`, and the compiler closure exports exactly one function of that name: `compiler.frontend.core.types.str_slice`, whose body was `s[start:end_idx]`. So every text `.slice(a, b)` in the closure was rebound to it. `s[a:b]` is `rt_slice`, which counts **code points**; `.slice(a, b)` is specified in **byte** offsets (`rt_slice_text_bytes`). Only the bare-method fallback a few lines below is gated by `is_builtin_receiver_type`; the lowercase-joined lookup is not.

`_sdn_strip_leading_comment_lines` computes a byte offset with `byte_at` and returns `source.slice(line_start, n)`. The old 00.common manifest had two em dashes (3 bytes, 1 code point each) in the comment block ahead of `project:`, so the cut landed 4 bytes late: the document began `ect:` instead of `project:`, and `get_path("project.name")` found nothing.

A closure without a `str_slice` function (any small probe, or anything built by the Stage 2 binary itself) lowers `.slice` to `rt_slice_text_bytes` and is correct. That is why every earlier probe was green.

## Evidence

- `gdb` on the Stage 2 binary (`pinned-3dd00937c329`), calling its own functions on the pre-reorder manifest with the `dependencies:` edge removed (2489 bytes, `project:` at byte 2141): `file_read` length 2489; `_sdn_strip_leading_comment_lines` length 344 (expected 348), text starting `ect:\n  name: simple-compiler-common`; `library_unit_decl_parse_v1` returns `Err("...: project.name is missing")`.
- `strace` of a Stage 2 build: its source scan reads the (already reordered) manifest with one `read(3, ..., 2529) = 2529`. Supporting only; the `gdb` length above is the direct evidence that `file_read` does not truncate.
- `objdump` of the Stage 2 binary: `_sdn_strip_leading_comment_lines` ends in `b compiler__frontend__core__types__str_slice`, which is `mov w3,#1; b rt_slice`. Call census: 1382 sites call `rt_slice_text_bytes`, 62 sites outside the core package call `...core__types__str_slice` (34 in `sdn/parser.spl`, the rest in `stable_id.spl`, `host_path.spl`, `bug.spl`, `structural_scalar_value_v1.spl`, HIR statement lowering and driver files).
- Exact producer, 3 s per build, probe importing the real `std.common.sdn.parser` and `compiler.frontend.core.types` (`parse(file_read(path))`, then `get_path("project.name")`). Without the two env vars the seed takes a different, much slower path:

  ```
  AUTH=<pinned>/.simple/storage/build/bootstrap/stage3/<triple>/stage2-runtime-authority
  SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_NO_STUB_FALLBACK=1 $AUTH/simple native-build \
    --backend llvm --runtime-bundle core-c-bootstrap --source src/compiler --source src/lib \
    --source <probe dir> --entry-closure --cache-dir <fresh dir> --entry <probe dir>/main.spl \
    --runtime-path $AUTH -o <out>
  ```


  | manifest bytes | before | after the workaround |
  |---|---|---|
  | pre-reorder manifest (two em dashes ahead of `project:`) | `project.name=[]` | `project.name=[simple-compiler-common]` |
  | same with the em dashes replaced by `-` | `simple-compiler-common` | `simple-compiler-common` |
  | current reordered manifest (`a17add1a2c0`) | `simple-compiler-common` | `simple-compiler-common` |

- Minimal shape, same producer: a closure holding `fn str_slice(s: text, start: i64, end_idx: i64) -> text: s[start:end_idx]` and `fn cut(source: text, a: i64) -> text: source.slice(a, source.byte_len())`; `cut("ab\u2014cd\u2014project: x", 10)` prints `ect: x`, while `.substring` prints `project: x`. With a `str_slice` returning `"HIJACK"`, `.slice` prints `HIJACK`.
- Stage 2 as producer (the Stage 3 path): a standalone probe with the new `str_slice` body prints `direct=[project: x] method=[project: x] ascii=[ell]`. The full-closure probe cannot be built by this Stage 2 binary with or without the change (`MIR shard ledger inventory does not match this build's sources`), so that check is not available.
- Seed interpreter: `sdn_parser_spec` 26/26 and `sdn_leading_comment_spec` 6/6 pass; `str_slice` through `compiler.frontend.core` returns `project: x` and `ell`.

## Workaround

REMOVED 2026-11-28. `src/compiler/10.frontend/core/types.spl`: `str_slice` had returned `s.substring(start, end_idx)` (byte offsets, lowered straight to `rt_slice_text_bytes`), tagged `@workaround`; with the seed fix deployed it is back to `s[start:end_idx]` and the tag is gone. The manifest reorder `a17add1a2c0` is reverted too; `src/compiler/00.common/simple.sdn` is back to the essay-first layout.

Removal evidence: the rebuilt Stage 2 at pin `f3cf72db4299` (seed fix `af6ed58435c` is an ancestor) ran `test_runner_build` on 2026-11-28 with the exact pre-fix failure step green — `[library-unit-dynlib] units=4 reused=0 built=4`, `phase=link state=succeeded` for `simple_test_runner` (`build/bootstrap/pinned-src/pinned-f3cf72db4299/.simple/storage/build/bootstrap/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/test_runner_build.log`) — plus the seed fix's `numeric_receiver_resolution_tests` cargo unit tests (7/7).

The manifest reorder `a17add1a2c0` had also avoided the failure, but only incidentally: with content on line 1, strip returns the source unsliced. A non-ASCII character ahead of any other `.slice` cut would still have misparsed.

## Open

- **Seed fix — IMPLEMENTED 2026-11-27, lane validation pending.** Both
  lowercase-joined lookups in `resolve_name_variants`
  (`src/compiler_rust/compiler/src/pipeline/native_project/imports.rs`) are now
  gated by `is_builtin_receiver_type`, so a builtin-receiver method
  (`str.slice`, `str.len`, `Array.is_empty`, ...) can no longer rebind to a
  same-spelled user free function through `str_slice` / `strslice` spellings;
  resolution returns `None` and codegen takes the builtin lowering, the same
  behavior every small probe (no `str_slice` in closure) already showed.
  User-type factory resolution through the same lookup is unchanged (positive
  control in the new tests). Regression coverage: three new tests in
  `numeric_receiver_resolution_tests` (`cargo test -p simple-compiler --lib
  numeric_receiver_resolution_tests`). The end-to-end check is done: a rebuilt
  Stage 2 at pin `f3cf72db4299` ran `test_runner_build` with the library-unit
  packaging step green (2026-11-28, log cited under Workaround), and the
  `str_slice` source workaround below is removed. The Cranelift ladders carry the same spelling
  (`codegen/instr/calls.rs:4966`, `closures_structs.rs:1594`) and are NOT
  gated — a Cranelift seed build did not reproduce on the minimal shape, so
  they were left alone; revisit if a Cranelift lane ever shows the symptom.
- **Sibling rebindings, same mechanism (proven).** With the same producer, a closure defining sentinel `str_len`, `str_char_at`, `str_index_of`, `str_starts_with`, `str_contains`, `str_ends_with` and `str_replace` has `s.len()`, `s.char_at(1)`, `s.index_of(..)`, `s.starts_with(..)`, `s.contains(..)`, `s.ends_with(..)` and `s.replace(..)` all return the sentinels (`len=-111 char_at=HIJACK_CHAR_AT index_of=-222 ...`); the seed interpreter runs the builtins. Calls into `compiler.frontend.core.types` from outside the core package in the Stage 2 binary (direct source calls not separated out): `str_starts_with` 1747, `str_len` 1457, `str_contains` 1016, `str_ends_with` 555, `str_replace` 525, `str_index_of` 187, `str_slice` 62, `str_char_at` 30. The one with a visible unit difference is `str_len`: it is `rt_string_len`, which returned the byte count (2489) for the em-dash manifest, while the interpreter's `.len()` counts code points (7 for an 11-byte text). Consequences were not examined.
- ~~No rebuilt Stage 2 has run `test_runner_build` with the workaround yet.~~ Done 2026-11-28: pin `f3cf72db4299` (contains the seed fix), library-unit packaging green (log cited under Workaround).
- The `compiler_cli_build` failure in the same verification (`FILE-WORKER-E-CLOSURE-INCOMPLETE`, `failed_modules=3347`) is a separate problem.

## History

The stage-2 verification of pinned `3dd00937c329`, which contains `9acdac6f849` (`mir_text_bytes_unresolved_inferred_trim_receiver_2026-10-23`), failed the same way:
- `test_runner_build` FAIL after 1550 s, with `library-unit dyn-lib packaging failed: src/compiler/00.common/simple.sdn: project.name is missing`.
- `compiler_cli_build` FAIL after 18732 s, with `FILE-WORKER-E-CLOSURE-INCOMPLETE: import-closure surface missing` and `MIR shard aggregate failure ... failed_modules=3347`.

The first run below used `06ba866385d5`.

## Observed

The stage-2 compiler-tests verification (pinned source `06ba866385d5`, aarch64) produced neither tool:

| Task | Result | Detail |
|---|---|---|
| `compiler_cli_build` | TIMEOUT | 21603 s, artifact `producer-failed` |
| `test_runner_build` | FAIL | All 321 objects compiled and linking started; then `error: focused native-build: library-unit dyn-lib packaging failed: src/compiler/00.common/simple.sdn: project.name is missing` |

## What is known

- `src/compiler/00.common/simple.sdn` does contain `project:` / `name: simple-compiler-common`.
- On the Rust seed interpreter, `library_unit_decl_parse_v1("src/compiler/00.common", <that file>)` returns `OK name=simple-compiler-common kind=library`. So the parser source is correct for those bytes.
- The only packaging path is `library_unit_manifest_closure_v1`, which calls `library_unit_manifest_parse_v1` and then `library_unit_decl_parse_v1` (`src/compiler/80.driver/driver_build/`). Empty content would be refused earlier as `missing manifest`, so the stage-2 path received non-empty text and `root.get_path("project.name")` then `as_str()` produced `""`.

## Open questions at filing time (answered above: neither)

1. A native miscompile of `SdnValue.get_path` / `as_str() ?? ""` in the stage-2 compiler.
2. `load` returning different, non-empty bytes, for example a different file or a truncated read.

To tell them apart, natively build a probe that prints `content.byte_len()` and the decoded name inside `library_unit_manifest_closure_v1`'s `load`. Run it from a tracked (not gitignored) path under the checkout, with a memory cap above the ~4.5 GB per-worker estimate.

## Consequence

No qualified self-hosted `SIMPLE_BIN` or test runner exists. This blocks native qualification of the Linux orchestrator rows (`doc/03_plan/agent_tasks/simple_orchestrator_status_20261126.md`).


## Shard Registration (2026-11-27)

- **Workaround site:** `src/compiler/10.frontend/core/types.spl:36-37` (`str_slice` was `s.substring(start, end_idx)`, tagged `# @workaround bug=stage2_test_runner_libunit_project_name_missing_2026-11-27`; REMOVED 2026-11-28, back to `s[start:end_idx]` after the seed fix was confirmed by a rebuilt Stage 2).
- **Seed fix commit:** `3850673f958` (`src/compiler_rust/compiler/src/pipeline/native_project/imports.rs`, `resolve_name_variants` gated by `is_builtin_receiver_type`).
- **Shard:** `doc/08_tracking/bug/db/stage2_test_runner_libunit_project_name_missing_2026-11-27.sdn` (`status=fix-implemented-verification-pending`, waiting for rebuilt Stage 2 passing `test_runner_build` end-to-end before retiring `str_slice` workaround).

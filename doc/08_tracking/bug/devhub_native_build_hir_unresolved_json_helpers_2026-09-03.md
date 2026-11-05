# devhub native-build fails in HIR: `unresolved name: json_object_get` (+89 more)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Date: 2026-09-03
- Status: OPEN
- Platform observed: Windows x86_64-pc-windows-msvc
- Severity: blocks the entire devhub compiler/native lane

## Repro

```sh
. scripts/setup/windows-msvc-bootstrap-env.shs
/d/win-p3-mmap/build/bootstrap/stage3/x86_64-pc-windows-msvc/stage2-admitted/simple.exe \
  native-build src/app/devhub/main.spl -o /tmp/devhub_native.exe
```
(admitted binary sha256 `fcf473728180d790bc6e15892c59cadf2f12600b4825575b30e3ff91c20bcf86`)

Exit status (read directly, not through a pipe): non-zero, ~52 s, no artifact
produced.

## Observed

`[ERROR] phase 3 FAILED` (HIR), 175 fatal lowering errors across 20 modules,
then `[ERROR] phase 3 FAILED (diagnostics unreadable: error array did not
survive transport)`.

Error census from the build log:

| count | error |
|---|---|
| 47 | `unresolved name: json_object_get` |
| 16 | `unresolved name: json_array_length` |
| 15 | `unresolved name: json_array_get` |
| 69 | `invalid export origin` |
| 16 | `unresolved type` |
| 2 | `unresolved name: kind` (see the sibling record below) |
| 2 | `unresolved name: print_raw` / `terminal_stdout_is_tty` |
| 1 each | `time_now_unix_micros`, `substring`, `rt_env_cwd`, `len`, `json_object_has`, `dir_walk_files` |

First fatal: `src/app/devhub/cmd_github.spl:18:5 unresolved name:
json_array_length`.

Poisoned modules include `app.devhub.{cmd_github,cmd_email,cmd_tasks,
cmd_daily_debug,cmd_lifecycle,errors,output,adapter_*}`, `app.io.*`,
`std.common.json.{parser,serializer,types}`, `std.string_core`, `std.log`,
`std.io_runtime`.

## Not a duplicate

This is **not** the known `bootstrap MIR lowering: assignment target has no
local binding` failure seen on `src/app/mcp/main.spl` — devhub never reaches
MIR; it dies one phase earlier, in HIR name resolution, on JSON helper
functions that the interpreter lane resolves fine.

## Interpreter lane is unaffected

`bin/simple.exe run src/app/devhub/main.spl --version` prints `devhub 0.1.0`
(exit 0), and 26 of 30 devhub unit specs execute. So the JSON helpers exist and
resolve under the interpreter; only the bootstrap/native front end fails to
resolve them.

## Cross-platform note

Nothing was changed by this record. The failing resolution is in the bootstrap
compiler front end, not in platform code, so it is likely reproducible on Unix
with the corresponding stage3 binary — unverified here (no Unix host in this
session).

## UPDATE 2026-09-03 — census above is STALE; 175 -> 21

Root-caused. The 78 `json_*` `unresolved name` errors and all 69
`invalid export origin` errors were ONE defect class: the phase-1 entry
closure never loads a facade's re-export owner modules, so `std.json` and
`std.file_system` were parsed as empty facades. Filed as
`entry_closure_drops_facade_reexport_owner_modules_2026-09-03.md`.

Repaired data-side (compiler fix still open, needs a stage2 redeploy):
- `6014aa5385d` — json facade owners declared as real `export use` edges
- `0a3963ca0d5` — file_system facade owners likewise

Re-measured with the same admitted Stage 2 binary, exit status read directly:

| stage | errors |
|---|---|
| before | 175 |
| after json facade fix | ~80 (all json families gone; file_system exposed) |
| after file_system fix | 21 |

Remaining 21, all OUTSIDE this record's scope and independently tracked:
- 11 `unresolved type: Id` in `src/std/common/search/{types,ranking}.spl` —
  `hir_generic_type_param_unresolved_cross_module_2026-09-03.md`
- 5 from `print_raw` in `src/lib/nogc_sync_mut/tui/terminal.spl:38` (2 of them
  the `terminal_stdout_is_tty` cascade into `src/app/devhub/output.spl:18`) —
  `print_raw_builtin_unknown_to_selfhosted_hir_2026-09-03.md`
- 2 `unresolved name: kind` in `src/app/devhub/errors.spl` —
  `implicit_self_field_read_unresolved_in_plain_fn_method_2026-09-03.md`
- 1 `time_now_unix_micros` — the same facade defect in
  `src/lib/nogc_sync_mut/io/__init__.spl`, deliberately not patched (see that
  record)
- 1 `rt_env_cwd` in `src/lib/nogc_async_mut/env/platform.spl:21` — unfiled

Still no devhub.exe: HIR is not yet clean, and separately the stage2 binary
SEGVs (rc=139) after `monomorphize` on programs that DO clear HIR — reproduced
on a 7-line json program. `[mir-lower] WARNING: unresolved method call
'to_float' / 'chr' / 'keys' lowered to const-0 placeholder` and
`[post-mono-verify] unhandled HirTypeKind variant at walk_type` both appear on
those runs, so any future "successful" devhub build is suspect until they are
addressed.

## Status 2026-11-05 — NOT REPRODUCIBLE on release/1.0.0 (defect class fixed)

Verified on branch `work/rel100-devhub-fixes-20261105` @ `c3b2271c310`:

1. **Data side (this record's "repaired data-side" commits) is merged here.**
   `src/lib/common/json/__init__.spl` now declares real `export use`
   owner-module edges (`common.json.{array_ops,object_ops,parser,path_ops,
   serializer,types,utilities,validation}.*`), and the file_system facade has
   likewise (facade-owner fix `0a3963ca0d5` reachable from HEAD).
2. **Compiler side is merged here.** `bb27a92a7a8` ("fix(compiler,lib): four
   native-build defects — devhub 175→21, MIR module globals, caret suite,
   diagnostics transport (#345)") is an ancestor of HEAD.
3. **Re-ran the original repro** with the tracked `bin/simple.exe` seed:

   ```
   bin/simple.exe native-build src/app/devhub/main.spl -o build/devhub-lane/devhub_native.exe
   ```

   The log contains **zero** `unresolved name` / `invalid export origin` /
   `unresolved type` lines — HIR name resolution, the phase this record's
   175-error census died in, is clean. The build proceeded deep into later
   phases and was killed at a 20-minute wall-clock cap during codegen; no
   artifact was produced in this session.
4. **Interpreter lane still healthy:** `bin/simple.exe run
   src/app/devhub/main.spl --version` prints `devhub 0.1.0` (exit 0), and the
   full `test/01_unit/app/devhub` suite runs 1046+ examples with only one
   unrelated, separately-explained failure (see below).

**Still open, tracked elsewhere (not this record):** the remaining 21-error
census and the post-HIR MIR/SEGV warnings named in the UPDATE above remain the
subject of the sibling records (`hir_generic_type_param_unresolved_cross_module`,
`print_raw_builtin_unknown_to_selfhosted_hir`,
`implicit_self_field_read_unresolved_in_plain_fn_method`, and the unfiled
`rt_env_cwd` item) plus the stage2 SEGV-after-monomorphize caveat.

**Suite note for the merge owner:** in the directory-mode unit sweep,
`test/01_unit/app/devhub/wiki_backend_routing_spec.spl` fails 15/1 while the
same file passes 16/16 when run alone. Root cause (verified by env diff and
stderr capture): the directory runner exports `SIMPLE_JIT_ENABLED=1` to route
children (single-file runs instead set `SIMPLE_EXECUTION_MODE=interpret`), so
the spec's last test — which spawns the real `bin/itf wiki --help` — executes
devhub through the seed JIT. The seed JIT then reports 23 pre-existing
`[CODEGEN-STUB-FALLBACK] body compilation failed` errors, all in
`src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/http_client/request.spl`
(`GlobalLoad: unresolved identifier 'request'` in `create_headers`,
`add_header`, `send_request`, `http_get/post/put/delete`, `response_*`),
unrelated to the `errors.spl` `kind` regression that test guards. None of the
23 failing functions are in `src/app/devhub/**`; fixing them belongs to the
http_client/seed-JIT lane. No source change was made for this record.


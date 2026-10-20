# False @cfg on a multi-line `use m.{` leaks its column-0 closing brace into the parse

- **Date:** 2026-10-20
- **Status:** open — tagged source workaround active; root fix on branch `work/p4p2-cfg-multiline-use-closer`
- **Found by:** p4-phase2 lane (Phase-4 tools built by the Phase-2 compiler, producer7 `87b9c74ff39`)
- **Source tree:** origin/release_phase3 `97aa8eb9e1f`
- **Producer identities:** `producer7-20261020/strict/simple-producer7-strict.exe`
  (llvm) and `p4-phase2-20261020/producer7-cl/simple-producer7-cl.exe` (cranelift)

## Failure

`native-build --entry src/app/cli/bootstrap_main.spl --source src/os ...` stops
in phase 2, on both backends:

```
error: parse error in .../src/os/kernel/loader/authenticated_fs_exec_submission_service_v1.spl: 876:1:unexpected token in expression: } '}'
[ERROR] phase 2 FAILED (3 recorded error(s))
```

The other two errors are in the sibling record
`p4p2_flat_parser_noinit_module_var_struct_and_fn_types_2026-10-20` and in the
dangling `impl Fat32Filesystem:` header, which the same commit deletes.

## Root cause

`src/compiler/10.frontend/core/parser_preprocessor.spl` handles a false `@cfg`
on a declaration that opens a bracket (`_pp_line_bracket_delta > 0`) by entering
`skip_until_dedent` with the bracket depth seeded. Inside that skip, it consumes
the line that closes the brackets only when that line ends in `:` or `{` (the
`) -> R:` header of a multi-line fn).

The closing line of a multi-line `use m.{ ... }` is `}` at the declaration's own
indent. That line brings the depth to 0, but it does not end in `:` or `{`, and
it is not deeper than the declaration. So the skip ends and the `}` is left in
the token stream.

The separate `skip_until_close_brace` branch that was written for this case is
unreachable, because a `{` line always takes the bracket-delta branch first.

A `true` @cfg is unaffected, which is why the x86_64 block parsed and the arm64
block at line 873 did not. `boot/init_services.spl` closes its brace on the
indented name line, so its closer is blanked by the indent rule and it parses.

## Workaround

Tagged `@workaround bug=p4p2_cfg_false_multiline_use_closing_brace_leaks_2026-10-20`
in `src/os/kernel/loader/authenticated_fs_exec_submission_service_v1.spl`: the
six gated uses are collapsed onto one line each. This is in commit `8b7cfa3a43c`
on `work/p4p2-os-parse-workarounds`. The original multi-line form is
`97aa8eb9e1f:src/os/kernel/loader/authenticated_fs_exec_submission_service_v1.spl:869-892`.

## Root fix

Branch `work/p4p2-cfg-multiline-use-closer`. A line that closes the excluded
declaration's brackets without starting a body is consumed and ends the skip.
A regression case is added to
`test/01_unit/compiler/frontend/when_block_target_cfg_spec.spl`. The fix needs a
producer rebuild before it can retire the workaround.

## Retirement

Once a producer built with the root fix is deployed, restore the multi-line form
and confirm that a bootstrap_main `--source src/os` build passes phase 2.

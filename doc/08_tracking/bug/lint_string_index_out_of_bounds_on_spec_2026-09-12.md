# `bin/simple lint` aborts with `string index out of bounds` on one spec file

- Status: OPEN (2026-09-12)
- Binary: `bin/release/aarch64-unknown-linux-gnu/simple`, sha256 `3d120a6f`
  (Rust seed, `Simple Language v1.0.0-rc.1`)
- Found by: lane L9 G3/G4 (`work/l9-g34-2026-09-12`), out of scope for that lane.

## Symptom

```
$ bin/simple lint test/01_unit/app/simple_lsp_mcp/lsp_query_owned_process_v1_spec.spl
error: semantic: string index out of bounds: index is 12072 but length is 12072
  (preview="# Owned-process launcher coverage for the persistent LSP que")
$ echo $?
1
```

No finding is printed and no `Found N error(s)` verdict line is emitted — the
linter dies instead of answering. The preview names the linted file's own
source, so a rule is reading one character past the end of the file buffer.

## Not a size boundary

Appending `\n# End of spec.\n` (12074 -> 12088 bytes) moved the numbers but not
the defect: `index is 12088 but length is 12088`. The overrun is always exactly
one past the end, at whatever the length happens to be, so it is content-shaped
rather than length-shaped.

## Not the file

The same file parses, type-checks and runs clean:

```
$ SIMPLE_EXECUTION_MODE=interpreter bin/simple test \
    test/01_unit/app/simple_lsp_mcp/lsp_query_owned_process_v1_spec.spl
SPEC FILE VERDICT: ... outcome=OK declared>=15 executed=15 passed=15 failed=0
```

## Nearby files that lint fine (same directory, same idioms)

| file | verdict |
|---|---|
| `test/01_unit/app/simple_lsp_mcp/lsp_query_session_runner_v1_spec.spl` | `Found 0 error(s), 4 warning(s)` |
| `test/01_unit/app/simple_lsp_mcp/lsp_query_session_v1_spec.spl` | `Found 0 error(s), 1 warning(s)` |

The sibling spec uses the same `expect(x == EnumV1.Variant).to_be(true)` idiom
and the same `describe`/`it`/`step` shape, so neither of those is the trigger.
The narrowest untested difference is the crashing file's final example, which is
the only one in the three that puts an `if ... : / else:` block inside an `it`
body, and the only one importing `app.io.minimal_runtime_ops.{cwd}`. Not
bisected — each lint run on this host costs 2-4 minutes.

## Impact

A file that cannot be linted cannot be gated. The failure is loud (exit 1), so
it does not silently pass, but any lane whose deliverable includes "lint the new
files" is blocked on that one file with no workaround.

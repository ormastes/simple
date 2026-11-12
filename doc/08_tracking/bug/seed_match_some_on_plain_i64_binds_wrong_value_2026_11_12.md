# Seed interpreter: `match <i64>: Some(x)` binds a wrong value

- id: seed_match_some_on_plain_i64_binds_wrong_value_2026_11_12
- status: verification-pending
- severity: P2 (silent wrong value)
- found: 2026-11-12, lane work/t32-mcp-names-20261112
- binary: phase-1 seed sha256 9ce8892528f9397a58e1c1c6f5a68a43640121fb38c509780a5fa57457c27f2e

## Repro

```
fn main() -> i64:
    val json = "{\"value\":\"alpha\"}"
    val r = json.index_of("\"value\":")   # r prints 1
    var a = -1
    match r:
        Some(j): a = j
        nil: a = -2
    print "a={a}"                          # prints a=3, expected 1
    0
```

`text.index_of` returns a plain `i64` (-1 on miss). Matching it with
`Some(j)` should either bind 1 or be rejected; the seed binds 3.
`if val idx = r:` binds 1 correctly.

## Impact

`t32_extract_field` (t32_mcp/json_helpers.spl) returned `lpha"` for
`{"value":"alpha"}`. Workaround landed: use `t32_find_text`. Same pattern
remains in `examples/10_tooling/trace32_tools/cmm_lsp/mcp_daemon.spl:116`.

## Fix direction

Either reject `Some(..)` against a non-Option scrutinee at check time, or make
the seed bind the payload the same way `if val` does.

## Resolution (2026-11-12)

Policy check: the Option-shape check on a non-Option scrutinee is a staged,
default-off diagnostic (`SIMPLE_DIAG_OPTION_PATTERN_SHAPE`, see
`option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md`); flipping it
to a hard error is an owner decision. The interpreter already binds the flat
Option encoding (the subject itself is the `Some` payload), so the fix makes
the compiled lane agree with it.

Root cause: the default `simple run` engine (HIR -> MIR -> JIT) lowered
`Some(j)` over a bare `i64`/`text` subject via `rt_enum_payload`, which
answers the nil sentinel for a non-enum (`j = nil`, `a = 3`). The interpreter
lane used by the test runner was already correct, which is why the defect
only showed under `run`.

Fix: `build_pattern_binding_stmts` (`hir/lower/stmt_lowering.rs`) binds the
subject local directly when the subject's static type is a never-Option
scalar/text (`never_option_type_name`).

Call sites: `t32_mcp/json_helpers.spl` workaround removed and
`cmm_lsp/mcp_daemon.spl` both use `index_of` + `< 0` (a plain `i64` is never
nil, so the old `nil:` arm could not catch a miss).

Spec: `test/01_unit/compiler/hir/match_some_on_plain_i64_binds_subject_spec.spl`
(old seed 5/6, fixed seed 6/6).

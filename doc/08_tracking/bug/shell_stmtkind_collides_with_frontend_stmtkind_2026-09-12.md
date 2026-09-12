# `os.apps.shell.shell_script.StmtKind` is shadowed by the frontend's `StmtKind` under co-compilation (2026-09-12)

- Status: OPEN (2026-09-12)
- Component: `src/os/apps/shell/shell_script.spl` (`StmtKind`) vs
  `src/compiler/10.frontend/parser_types_expr.spl:664` (`StmtKind`)
- Impact: blocks the sosh dialect adapter for the EGL package 4 parse-result
  provider seam; `ScriptEngine.parse` breaks whenever both modules are
  co-compiled

## Symptom

Importing `os.apps.shell.shell_script` and any module that pulls the compiler
frontend into the same program makes the shell's own parser unusable:

```
semantic: unknown variant or method 'Command' on enum StmtKind
```

The failure is inside `shell_script.spl` itself (`_make_empty_stmt(StmtKind.X)`),
not in the importing code — the importer need never name `StmtKind`.

## Minimal reproduction (6 lines, verified on this host)

Run as a throwaway spec at `test/01_unit/compiler/driver/zz_probe3_spec.spl` and
then removed; it is NOT in the tree. Recreate it verbatim to reproduce:

```
use std.spec.{describe, it, expect}
use os.apps.shell.shell_script.{ScriptEngine}
use compiler.driver.parse_result_provider_seam_v1.{PARSE_DIALECT_SIMPLE_V1}

describe "probe3":
    it "parses a sosh line with the seam module in the graph":
        val stmts = ScriptEngine.new().parse("echo hi\nX=1\n")
        expect(stmts.len()).to_equal(2)
        expect(PARSE_DIALECT_SIMPLE_V1).to_equal(1u32)
```

`bin/simple test` on that file: `1 total, 0 passed, 1 failed`, the message
above. Deployed seed `bin/release/aarch64-unknown-linux-gnu/simple`, 50093192
bytes, 2026-09-06 09:59:11 +0900.

Dropping the seam import and keeping only `compiler.core.tokens` makes the same
call PASS (`stmts=3`), so the trigger is the frontend entering the program
graph, not the shell module alone.

## Cause

Two enums share the name and neither is namespaced at resolution time:

- `src/os/apps/shell/shell_script.spl:19` — `enum StmtKind` (Command, If, While,
  For, Case, FnDef, Assign, Source, BreakStmt, ContinueStmt, ReturnStmt)
- `src/compiler/10.frontend/parser_types_expr.spl:664` — `enum StmtKind`

Enum-variant resolution is program-global by enum NAME, so the frontend's
definition wins for every module in the program, including `shell_script.spl`.

**An aliased import cannot help**, because the collision fires inside
`shell_script.spl` itself, before any importing code runs. A separate probe with
`use os.apps.shell.shell_script.{StmtKind as ShellStmtKind}` and
`case ShellStmtKind.If:` failed with the same class of error
(`unknown variant or method 'If' on enum StmtKind`), consistent with that — it is
corroboration, not independent evidence about aliasing.

The same shape exists for `TokenKind`: `std.common.sdn.lexer` vs
`src/compiler/10.frontend/core/lexer_types.spl:51` and
`src/compiler/70.backend/arch_rules.spl:202`. The SDN dialect adapter works
around it by never naming a token kind (SDN punctuation tokens carry their
character as their `text`), which is possible there and is NOT possible for
sosh: a statement kind has no other observable.

## Fix

Either make enum-variant resolution respect the importing module's binding
(the real fix, compiler-side), or rename one of the two enums. Renaming
`src/compiler/10.frontend/parser_types_expr.spl` is not available to an ordinary
lane — that file is owned by a concurrent Codex session. Renaming the shell's
`StmtKind` to `ShellStmtKind` touches 33 occurrences across 8 files under
`src/os/apps/shell/` and needs that area's owner.

## Registration

`doc/08_tracking/bug/bug_db.sdn` is owned by a concurrent Codex lane (it appears
in this wave's off-limits set), so this record is a standalone `.md` and is NOT
registered in the bug DB. Whoever lands this should run `bin/simple bug-add` /
`bug-gen` to register it.

## Consequence right now

`src/compiler/80.driver/parse_dialect_adapters_v1.spl` ships the SDN dialect
only. The sosh adapter is not written, because no spec that exercises it through
the seam can load.

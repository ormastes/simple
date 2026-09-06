# Native tool builds fail on two compiler gaps and lose their own diagnostics

**Date:** 2026-08-31
**Status:** OPEN — measured, not yet fixed
**Lane:** Windows MSVC host, `bin/simple.exe native-build`

## Summary

With the Windows native-build lane repaired (a hello world now produces a
running 12.3 MB PE), the Stage 4 tool closures were attempted. Two of three
fail, at **different pipeline stages**, and neither failure is
Windows-specific — both are language/lowering gaps that would reproduce on
Linux. A third, separate defect truncates the diagnostics needed to debug
them.

## 1. lint closure — HIR lowering, unresolved names

```
error: HIR lowering error in src/app/io/cli_lint_commands.spl:
  unresolved name: read_file at src/app/io/cli_lint_commands.spl:18:8
  unresolved name: easyfix_id_text at ...:18:8
  unresolved name: easyfix_description_text at ...:18:8
```

Every reported position is `18:8`, i.e. the import site, not the use site —
so this is import/module-surface resolution, not three independent typos.
Entry: `src/app/cli/lint_entry.spl` -> `app.io.cli_lint_commands`.
Measured cost before failure: ~35 min, worker RSS ~2.0 GB.

## 2. MCP closure — MIR lowering, tuple-destructuring assignment

```
error: MIR lowering error: unsupported MIR assignment target:
  HirExprKind::TupleLit([HirExpr(...)])
```

MIR lowering has no case for assigning to a tuple literal pattern
(`a, b = f()` / `(a, b) = ...`). This is a **missing language-feature
lowering**, not a porting gap: the same source would fail on any host.
Entry: `src/app/mcp/main.spl`. Reached parse 34/61 before failing.

## 3. native-build loses its own stderr (blocks debugging 1 and 2)

```
[native-build] WARNING: could not save full stderr to
  /native-build-stderr-22972.log; only the excerpt below survives
...226217 bytes omitted from the middle...
```

The path is **root-relative** (`/native-build-stderr-<pid>.log`), which is
unwritable on a Windows host, so the full log is dropped and only a
middle-elided excerpt survives. 226 KB of diagnostics were lost from a
single run. This is a Windows-path defect in the diagnostic path itself and
should be fixed FIRST — it is the reason 1 and 2 are known only by excerpt.

## Not affected

`test_runner_new` was still building when its runner was stopped for disk
reasons; its result is unknown, not failing. `doc` has no standalone entry
(`src/app/doc_coverage/` is a library; `doc-coverage` is served by the full
CLI binary).

## Evidence

Logs (excerpt-only, per defect 3): scratchpad `lint_build.log`,
`mcp_build.log`. Host: MSYS2 mingw64 gcc, PATH set so MSYS2's mingw64
precedes Git-for-Windows' (otherwise cc1 crashes on every input — see
`llc`/gcc discovery notes in the Windows bootstrap records).

## Unix impact

None of the three is Windows-only in *cause*; defect 3 is Windows-only in
*symptom* (the root-relative path happens to be writable on Unix, so the
diagnostics survive there and the bug is invisible).

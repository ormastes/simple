# Native tool builds fail on two compiler gaps and lose their own diagnostics
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Round-10 verdict note (2026-11-06)
Defect 3 (root-relative stderr spill path): ALREADY-FIXED - src/app/cli/native_build_main.spl (spill_root) uses SIMPLE_NATIVE_BUILD_CACHE_DIR/diagnostics, TMPDIR, TEMP or TMP before /tmp. Defects 1 (lint closure unresolved import names) and 2 (MIR lacks tuple-literal assignment-target lowering) are feature-sized; each repro is ~30 min of native-build. Verification-pending command: Phase-3 binary native-build --entry src/app/cli/lint_entry.spl and src/app/mcp/main.spl.

---

## Addendum 2026-11-11 (lane boot7) — SUPERSEDED (fix-implemented; one related live finding)

All three defects are addressed on the release tip; per the bug DB row
(`doc/08_tracking/bug/db/native_build_tool_closures_hir_mir_gaps_2026-08-31.sdn`,
updated by d790c7102a30 / PR #8056) the row status is
"fix-implemented-verification-pending … native lint-closure rerun pending".

- **Defect 3 (root-relative stderr spill on Windows): FIXED.** Source-verified at
  tip b364745fdbf8: `eprint_bounded` spill_root prefers
  SIMPLE_NATIVE_BUILD_CACHE_DIR/diagnostics, then TMPDIR/TEMP/TMP, before /tmp
  (native_build_main.spl:632-652). Confirmed again while triaging
  native_build_stderr_spill_drops_fatal_error_2026-09-01 (same function).

- **Defect 2 (MIR lacked tuple-literal assignment-target lowering): FIXED.**
  `mir_lowering_stmts.spl` now has `case TupleLit(elements):
  self.lower_tuple_destructuring_assign(elements, value_local, op)` at :2724-2725,
  with a real implementation at :2431-2466 (emit_get_field per element +
  lower_assign), introduced by merge 820631c6e5c7 (PR #7545). The reported
  "unsupported MIR assignment target: TupleLit" no longer fires; a program using
  `(c, d) = t` compiles and runs.

- **Defect 1 (lint-closure unresolved import names): FIX IMPLEMENTED, closure
  rerun pending.** Root cause per PR #8037 (0db8bd34d668, merged 14ef71e856eb):
  the readers were file-private, "the same shape that made the native
  lint-closure build fail with 'unresolved name: read_file' at the import site"
  — made pub, with regression spec
  test/01_unit/app/io/cli_lint_imports_pub_spec.spl.

Seed-smoke verifications (2026-11-11, seed 0791c2b7f4a7, interpreter mode):
- `bin/simple.exe test test/01_unit/app/io/cli_lint_imports_pub_spec.spl
  --mode=interpreter --no-cache` — 3/3 PASSED (defect 1 regression).
- `bin/simple.exe test <probe with (c,d) = t> --mode=interpreter --no-cache`
  PASSED with correct values (defect 2 lowering accepted, correct on the
  interpreter engine).
- AOT end-to-end reruns (`native-build --entry src/app/cli/lint_entry.spl` and
  `--entry src/app/mcp/main.spl`) remain PENDING — native/entry-closure builds
  are forbidden in this lane; grant needed for those two commands.

### Related live finding (not one of this doc's three defects)

While probing defect 2, the SEED's JIT path (the default engine for
`simple run`; selected by SIMPLE_EXECUTION_MODE, not by `--mode`) miscomputes
the very construct defect 2 added: `(c, d) = (10, 20)` yields `80 160`
(exactly `v << 3`, the raw TAG_INT word delivered un-untagged — same class as
the FIXED `jit_tuple_get_returns_raw_tagged_word_to_i64_sink_2026-08-17`,
fix ee815637f72, which typed `.get()` results but did not cover the
destructuring-assign path). The interpreter engine
(`SIMPLE_EXECUTION_MODE=interpret`, and `simple test --mode=interpreter`)
computes `10 20` correctly, as do whole-tuple assign, array destructuring
assign, and `t.0` reads on both engines. Fix site is the seed-side lowering of
tuple destructuring assignment (unbox before the i64 store), not the
pure-Simple MIR path this doc tracks. Recorded here for routing; the pure-Simple
AOT path is unverified in-lane (blocked, see above).

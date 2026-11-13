# lintA findings (lane: src/compiler)

Branch: work/lint-compiler-20261113 (base e86a4a2e8ba)
Lane scope: src/compiler/**/*.spl (2,660 files). Lint throughput measured at ~25-40 s/file
(cold parse of the import closure per invocation), so a full-tree serial lint pass exceeds
20 h; this lane linted broad-closure roots (span, lint main, backend) and fixed the warnings
attributed to src/compiler paths.

## Method note (warning attribution)

`bin/simple.exe lint <file>` emits warnings for the whole import closure of <file>, with
`-->` attribution to the real file:line for W-STR-BRACE-001 / export-use-star, and compact
`file:line:col: warning[CODE]` lines for W0404/W0406/W0407/REQC004/export_outside_init.
[visibility-warning], [gc-warning] and co-compiled warnings are emitted as single-line
summaries with NO file:line attribution in this output mode.

## CRASH

None observed. No lint run returned rc>=128 and none hung past the 60-120 s timeouts used.

## ERROR-not-warning

1. `error[W-ANY-NOTRUN]: NOT CHECKED: the Any rules (mask 'dfr') did not run on this file —
   'check' exited 1 without writing its any-rules report (no check worker? set SIMPLE_BINARY)`
   — emitted for every linted file in this environment (repro: `./bin/simple.exe lint
   src/compiler/90.tools/lint/main.spl </dev/null` without SIMPLE_BINARY set). Classified as
   missing/incomplete diagnostic infra: the error text tells the user to set SIMPLE_BINARY,
   but the lint driver itself spawned the check without propagating its own binary path;
   the error is attributed to the linted source file (line 1:0), which misleads. Suggest:
   lint should pass its own exe path to the check worker automatically, or downgrade to a
   single upfront infra note.

## SILENT-GAP / diagnostic-infra gaps

1. Span drift on escape-heavy lines: W-STR-BRACE-001 `-->` column is exact for plain lines
   but drifts up to ~20 columns on lines whose string contains backslash escapes (e.g.
   src/compiler/90.tools/lint/rules/windows_c_compiler_selection_rule.spl:172-173, sed
   script with `\\{0,1\\}`; 35.semantics/lint/riscv_rtl_debuggability_lint.spl:264,267).
   The message column and `-->` column also differ by a constant 2. Spans should be computed
   post-unescape or the diagnostic should carry a byte offset.
2. [visibility-warning] / [gc-warning] / co-compiled summaries carry no file:line, so they
   cannot be fixed at scale without per-file lint passes; they also re-emit the entire
   cross-module set on every lint invocation (e.g. 78 visibility + 15 gc + 4 co-compiled
   identical lines regardless of the file being linted). Consider emitting them once with
   locations, or gating behind --verbose.
3. Co-compiled same-signature collision (143 symbol names listed in one warning,
   decl_attrs pass) is a single aggregated line; the env-var escape hatch
   (SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1) is only mentioned in passing.

## Fixed in this lane (src/compiler-attributed only)

- W-STR-BRACE-001: 88 sites across 33 files — flagged `{` converted to `{{` at the
  attributed location; valid `{name}` interpolations untouched (linter only flags invalid
  expressions; behavior-preserving because invalid interpolations were already kept
  literal).
- REQC004: 1 site (src/compiler/70.backend/backend.spl:41) — `case _:` converted to the
  established idiom `case _("all other kinds fall back to the JIT interpreter"):`.

## Deferred (not fixed in this lane)

- "Avoid 'export use *'" (25 sites) and W0407 wildcard export (10 sites): replacing with
  explicit name lists requires deriving each target module's pub surface; not safely
  scriptable in the timebox. Sites recorded in lint worklist.
- export_outside_init (7, src/compiler/70.backend/backend.spl:56-63), W0406 wildcard
  imports (3, backend.spl:16-19), W0404 (1, 90.tools/lint/main.spl): module-surface
  restructure — deferred as behavior-adjacent.
- [visibility-warning] / [gc-warning] / co-compiled attributed to src/compiler files:
  not actionable from summary-only output (see SILENT-GAP 2); owners in src/lib and
  src/app belong to other lanes.
- Full-tree sweep: 2,660 files at ~25-40 s/lint → needs a lint server/caching mode or a
  farm; recommend follow-up lanes keyed off the worklist pattern.

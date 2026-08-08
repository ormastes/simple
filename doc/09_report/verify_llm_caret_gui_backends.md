# Verification Report: LLM Caret GUI Backends

Date: 2026-07-19

## Passing evidence

- `gui_metal.spl` and `main.spl` pass the self-hosted Simple checker.
- Native input model: 3 examples, 0 failures.
- Pure-Simple SPipe docgen completed after fixing chained string dispatch; the
  generated manual contains 3 active scenarios and 0 pending/skipped tests.
- Electron 42.5.0 launched the canonical shell at `127.0.0.1:8330`; Playwright
  delivered visible input and click events, verified `test` → `hello`, restored
  focus, and retained a semantic screenshot.
- Numbered-artifact, direct-env-runtime (working/staged), rendering-source-
  coupling, whitespace, stub-pattern, and spec-layout audits pass.

## Failures

- **NFR-003 / NFR-005:** the final bounded Metal attempt emitted `html-ready`
  and `layout-start`, then blocked inside
  `simple_web_layout_render_html_draw_ir`. It never reached layout completion,
  backend resolution, Engine2D readback, or native presentation. The renderer
  is concurrently dirty in the unrelated WM/theme lane and was not modified.
- **Maintainability:** touched files `src/app/llm_caret/main.spl` (830 lines) and
  `src/app/spipe_docgen/spipe_docgen/generator.spl` (948 lines) exceed the
  verifier's 800-line limit; proposed extraction files were removed by a
  concurrent worktree update and are not present in the reviewed snapshot.
- **Production wrapper:** tracked `bin/caret` executes the raw source entrypoint
  through `simple run`, rather than a cached compiled Caret artifact.
- **Trace/manual evidence:** REQ-001/003/007 lack unambiguous executable mapping,
  the generated manual folds the primary flow, Electron lacks a retained event
  protocol artifact, and Metal has no screenshot/readback evidence.
- **Canonical tests:** diagnostic `simple run` invocations were not release
  evidence; the final tree still needs passing `bin/simple test ...
  --mode=interpreter` runs and regenerated zero-stub documentation.

## Result

`STATUS: FAIL` — no commit, rebase, or GitHub push is authorized until all
failures above are resolved and the independent verifier returns PASS.

# `Option<T>` becomes unresolvable when a module using it co-compiles with `provider.spl`'s large backend graph

**Found:** 2026-09-05, lane A7 (Caret GUI workbench, `caret_workbench` goal).
**Status:** worked around in lane code, NOT fixed in the compiler. Filed per
AC-7 (file a bug record for every defect found and not fixed).

## Symptom

Calling a function that pattern-matches on the builtin `Option<T>` type, defined
in a module imported transitively by `app.llm_caret.gui`, fails with:

```
error: semantic: class `Option` not found in this scope
```

This happens ONLY when the calling program also imports
`app.llm_caret.provider` (which pulls in `codex_cli`, `opencode_cli`,
`openai_api`, `openai_compat`, `local_torch`, and
`std.gc_async_mut.slang.entrypoints.llm` — a large backend graph). `Option<T>`
resolves fine:
- in the exact same file that imports `provider.spl` (verified: a local
  `fn find_it(...) -> Option<i64>` defined and matched in `main()` alongside a
  `provider` import works),
- across a module boundary, when the module using `Option<T>` is small
  (verified: a two-line helper module doing the same lookup works fine
  alongside a `provider` import),
- when the workbench modules (`gui_layout.spl`, `gui_page.spl`) are compiled
  WITHOUT `provider.spl` in the program (verified via
  `build/nb/fixtures/probe_gui_workbench.spl`, 0 failures).

It reproduces reliably once `provider.spl` is imported together with a
cross-module function returning `Option<T>` that is itself called from a chain
of several functions in the same file, each also using `Option<T>` for a
DIFFERENT `T` (here: `Option<SessionView>` and `Option<SessionUiState>` in the
same `gui_page.spl`). This smells like a generic-monomorphization collision
under a large co-compiled program — consistent with the several
`compiler_cross_module_private_symbol_collision` warnings already emitted for
plain (non-generic) symbols (`env_get`, `shell`, `process_wait`,
`file_read_text_at`, `process_run_with_limits`) in the same build.

## Minimal repro fixtures (not committed — recreate under `build/nb/fixtures/`)

```simple
# fails:
use app.llm_caret.provider.{LLMResponse, dispatch_send}
use app.llm_caret.gui.{caret_gui_html}   # gui.spl -> gui_page.spl uses Option<SessionView> AND Option<SessionUiState>

fn main():
    val page = caret_gui_html()
    print "OK len=" + page.len().to_text()
```
vs a two-line cross-module `Option<i64>` helper alongside the same `provider`
import, which succeeds. Full trace of the bisection is in this lane's session
transcript (2026-09-05); re-run the two probes above to reproduce.

## Workaround shipped in this lane

`src/app/llm_caret/workbench/gui_layout.spl` (`SessionUiLookup`) and
`src/app/llm_caret/workbench/gui_page.spl` (`SessionLookup`) each define a
dedicated `{found: bool, value: T}`-shaped struct instead of returning
`Option<T>`, specifically to avoid this trigger. This is a workaround, not a
fix — the underlying compiler defect (root cause not isolated further; likely
in generic-type resolution/monomorphization for programs with many
co-compiled modules) is still present for any other module that tries to use
`Option<T>` in the same position.

## Unblock condition

Isolate why the builtin `Option` type binding is lost specifically when (a)
`provider.spl`'s import graph is present AND (b) the same file uses `Option<T>`
for more than one concrete `T`. A fix removes the need for the
`SessionUiLookup`/`SessionLookup` workaround structs above.

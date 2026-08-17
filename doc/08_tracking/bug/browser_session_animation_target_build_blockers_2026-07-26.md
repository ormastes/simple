# BrowserSession animation target build blockers

- **Date:** 2026-07-26
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Scope:** production execution of the HTML/CSS/Simple Script/JavaScript
  animation fixture

## Reproduction

Fixture:
`test/fixtures/browser_script_css_animation/main.spl`

The fixture opens one page, proves Simple Script execution, renders CSS to a
red Engine2D frame, advances the monotonic page clock to 16 ms, runs
`requestAnimationFrame`, mutates the DOM from JavaScript, and requires a
different blue Engine2D frame.

Observed with the existing probe path `build/native_probe/simple`:

1. The probe identifies itself at runtime as a Rust-built bootstrap seed, so
   it is not valid production evidence despite its path/name.
2. Interpreter test mode parsed and started the focused spec, then timed out
   after 180 seconds without completing the 64x48 two-frame render.
3. Native test mode and direct `compile` delegated to the configured Rust seed;
   that seed received no source argument and rejected the command.
4. Direct pure-Simple `native-build --entry-closure` reached BrowserSession.
   Three pre-existing unsupported source forms were normalized (two multiline
   conditional expressions and tuple destructuring).
5. After those parser errors were removed, the isolated one-file entry-closure
   build produced no target or diagnostics before the 240-second bound.
6. The deployed
   `bin/release/x86_64-unknown-linux-gnu/simple` is byte-for-byte identical to
   `src/compiler_rust/target/bootstrap/simple`, despite being the canonical
   release path.
7. The standalone fixture could not reach `main`: the release/seed binary and
   the existing pure-Simple `build/bootstrap/stage2_memfix/simple` both rejected
   the documented run mode with `semantic: unknown argument 'interpreter'`.
   The release/seed attempt emitted 9.8 MB of diagnostics first.
8. A direct `build/native_probe/simple run` attempt likewise selected
   interpreter mode internally, emitted over 8 MB of misleading current-source
   diagnostics, and ended with the same unknown-mode error before `main`.
9. The genuine staged pure-Simple artifact at
   `build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple` identifies itself as
   a bootstrap compiler and exposes compile flags only; it has no source
   `run`/`test`/`check` surface that can execute the fixture.
10. Its supported `native-build` surface was then used directly with Cranelift
    and only the fixture entrypoint. Build cycle 1 stopped on enum-variant
    `if val` parsing in `browser_session.spl`; cycle 2 reached eight identical
    failures in `browser_session_runtime.spl`. Rewriting those valid compact
    patterns as `match` let cycle 3 reach the shared JS engine.
11. Cycle 3 stopped on the same parser defect at lines 162, 324, and 334 of
    `src/std/nogc_sync_mut/js/engine/interpreter_async.spl`. The mandatory
    three-cycle cap was reached, so no fourth source workaround or bootstrap
    was attempted.
12. Root cause in `parser_stmts.spl`: qualified enum constructors are
    represented as `EXPR_METHOD_CALL`, but statement- and expression-level
    `if val` admitted only `EXPR_CALL` and `EXPR_IDENT`. Both parsers now admit
    and desugar `EXPR_METHOD_CALL`; existing
    `test/shared/types/pattern_matching_spec.spl` coverage already exercises
    `if val MyOption.Some(v)`.
13. Three bounded compiler-production attempts followed with stub fallback
    disabled. The shared-worktree attempt reached link but found concurrent
    conflict markers in `src/runtime/runtime.h`. A clean detached-worktree
    attempt accepted the parser fix through object generation but the
    `core-c-bootstrap` link lacked the compiler/Cranelift runtime ABI. A final
    attempt using the existing genuine full CLI emitted no log or target for
    three minutes and was terminated. Caches and logs were preserved; no
    fourth compiler build was started.
14. A final direct source-run probe with that existing full CLI still
    delegated to `/usr/bin/simple_seed`, emitted millions of misleading
    diagnostics, and stopped before `main` on an unlocated
    `browser_session_runtime.spl` parse error (`expected Fn, found Else`).
    One malformed closing-call indentation found in the runtime source was
    corrected, but one bounded rerun produced the identical parser result.
    No further compiler/build retry was made.
15. The production hosted loop now initializes BrowserSession for displayed
    windows before input and advances its rAF/timer clock from a content-local
    host monotonic epoch. Its focused integration scenario requires a
    Simple-Script-created CSS red frame and a distinct JavaScript-rAF blue
    Engine2D frame at 16 ms. This source fix remains unexecuted until the
    genuine pure-Simple target lane below is restored.

## Required fix

Finish a bounded pure-Simple compiler link using an ABI-complete supported
runtime lane; the enum-variant parser source fix is present but not yet in an
executable. Do not fall back to the Rust seed. Separately fix native
test/compile dispatch so it preserves the source argument, accepts the
documented interpreter mode, and never silently selects the seed. Restore a
genuine pure-Simple executable at the canonical release path before accepting
the two-frame render result as production evidence.

# Seed interpreter regression: qualified `Span.empty()` dispatches to `empty(shape)`

**Status:** root cause fixed and bootstrap seed rebuilt on 2026-07-16. The
four missing `core-c-bootstrap` owners now have a source fix plus
archive-symbol evidence. The third and final bounded full-CLI rebuild exposed
a separate pure-parser tuple-destructuring gap; no candidate reached seedless
runner admission.

## Symptom

A freshly-built seed can fail during the first HIR declaration with:

```
error: semantic: function expects argument for parameter 'shape', but none was provided
```

The focused font runner reached this after parsing its six-module closure and
entering HIR declaration for `sffi/cli.spl`.

## Confirmed root cause

The parser lowers ordinary `Span.empty()` dot syntax to `Expr::MethodCall`, not
to the previously investigated `Call(Path)` or `Call(FieldAccess)` routes. The
method dispatcher treated any identifier absent from the local environment as
a module and immediately called a same-named bare function. An imported
`Span` can be present in the class registry but absent from that environment,
so the fallback selected the unrelated tensor `empty(shape)` with zero args.

The shared guard now permits the bare module fallback only when the receiver is
absent from both the environment and class registry. The focused regression
constructs exactly that state: `CollisionSpan` remains in `classes`, is absent
from `env`, and competes with a bare `empty(shape)`. An env-gated trace records
the MethodCall receiver/argc and selected function owner/parameter names only
for `empty`.

## Impact (critical for the redeploy)

The frontend defect no longer blocks HIR/native-build discovery. The focused
font evidence runner is still unavailable until the corrected core-C archive
is rebuilt into a new candidate, so pure-Simple SSpec calibration remains
pending.

## Disproven fixes

The pushed `Path` candidate consults `CLASS_OVERLOADS` and suppresses a bare
fallback only when the receiver is already recognized as a type. It passes its
small `CollisionSpan.empty()` probe but does not fix the real closure. Three
additional experiments were applied, rebuilt, traced, and then reverted because
the real failure remained unchanged:

1. Move the `FieldAccess` bare-function fallback after static recovery.
2. Remove the early `Path` bare-function fallback.
3. Preserve `Type__method` exports for selected group imports.

Retained logs:

- `build/font-runner-fieldaccess-fixed/native-build.log`
- `build/font-runner-path-fallback-removed/native-build.log`
- `build/font-runner-group-static-import/native-build.log`

Each ends with bare `empty`, exit 1, and no runner artifact. Do not repeat these
three experiments without new dispatch-owner evidence.

## Verification and next blocker

- `cargo check -p simple-compiler --tests` passes.
- `cargo build --profile bootstrap -p simple-driver` passes; rebuilt seed
  SHA-256: `a7fa5348b1be7fb8652a0742f44c0b575870e634ec500c25b6efe1269d716b4b`.
- `build/font-runner-methodcall-fixed/cycle1-native-build.log` proves the
  missing-`shape` diagnostic is gone and discovery advances to the wrapper.
- Parenthesizing the wrapper's documented multi-line boolean grammar advances
  native-build through parse and object generation.
- The final retained attempt,
  `build/font-runner-methodcall-fixed/native-build.log`, reaches link and fails
  only on `rt_getpid`, `rt_process_wait`, `rt_process_run_timeout`, and
  `rt_string_rfind` missing from `core-c-bootstrap`.
- The core-C source list now reuses `runtime_process.c`, `runtime_fork.c`, and
  `runtime_memtrack.c`; core compatibility owns `rt_getpid`/`rt_process_wait`,
  and the tagged-string owner implements `rt_string_rfind` beside
  `rt_string_find`.
- A direct build of the canonical Linux source list proves the archive exports
  all four symbols. Its C contract compile then exposed and fixed an unrelated
  missing delay argument in an existing HTTP fixture.
- Rust test harness startup remains independently blocked before test execution
  by its existing undefined `spl_arg_count`/`spl_get_arg` link baseline.

## Full-CLI bootstrap follow-up (2026-07-16)

The first bounded full-CLI build passed Stages 2 and 3, then exposed a pure
frontend gap at Stage 4: flat module parsing consumed `pub` but did not skip the
resolver-owned `mod` declaration. `parse_module_body` now skips both public and
private dotted child-module declarations, and the regression asserts that the
following function remains visible and that parsing records no error.

The second bounded build again passed Stages 2 and 3 and advanced substantially
farther through Stage 4. It exposed the next pure lexer gap on raw triple-quoted
docstrings (`r"""..."""`). `CoreLexer.scan_raw_string` now recognizes the
combined delimiter, preserves dollar signs and backslashes literally, consumes
the closing triple delimiter, and reports unterminated input. A focused lexer
regression covers the literal behavior.

Stage 4 in that cycle spent roughly 50 minutes compiling one binary. A sample
at 35:59 CPU showed 3,589,152 KiB RSS. The final bounded cycle subsequently
exceeded one hour of continuous CPU time and 5,619,552 KiB RSS without emitting
a phase-progress message or candidate ELF before failing in phase 2. This is a
concrete bootstrap performance bug: native-build
needs phase timing and memory attribution, followed by an incremental/cache or
peak-memory fix. It is not acceptable to hide the cost by falling back to the
Rust seed.

The third build was the final verify/fix cycle allowed for this session. It
failed parsing `src/compiler/15.blocks/blocks/unified_registry.spl:74` at
`for name, lit_def in literals_config.custom`: the pure Stage-4 parser expected
`in` after `name` and rejected the comma. Retain that diagnostic and continue
the tuple-destructuring grammar fix in a fresh bounded session; do not restart
bootstrap here. A later successful candidate must still be copied without a
sibling seed and run a real focused SSpec through `test` before admission.

## Fresh bounded cycle (2026-07-16)

The shared `for` target parser now accepts the repository's unparenthesized
tuple form (`for name, value in ...`) through the same tuple encoding already
used by the parenthesized form. The first retained retry stopped during
discovery on six one-line mutating methods in
`src/app/test_daemon/session_broker.spl` with `expected Fn, found Assign`.
Because assignment is a side-effecting statement rather than an expression,
those methods now use canonical indented bodies. Keep the compact assignment
form recorded as unsupported until both discovery and native execution gain a
focused grammar gate; do not silently reintroduce it.

The second retry used the retained Stage-3 compiler directly without the
wrapper's Stage-4 environment. It reached final link after closure discovery
accepted the canonical session-broker method bodies, but linked the
non-Stage-4 core-C archive and therefore reported the expected broad
hosted-symbol omissions. This does not prove that a compiler containing the new
tuple parser was built: the retained Stage-3 binary predates that source patch.
The invocation is not a runtime-bundle defect and must not be repeated; the
canonical environment sets `SIMPLE_BOOTSTRAP_STAGE4=1`, forces the whole
archive, and clears the runtime override.

The third and final retry used that exact canonical environment. After roughly
one hour and more than 5 GiB RSS, its in-process phase repeated the old
`unified_registry.spl:74` comma diagnostic. Inspection of the retained Stage-3
binary shows that it contains the old `parse_for_stmt`/`parse_for_expr` logic
and no `parse_for_binding_names` helper; its timestamp also predates the tuple
source patch. Native object caching occurs after parsing and therefore cannot
explain this parse-time diagnostic. This is not grounds for a fourth retry. A
fresh bounded session must rebuild Stage 2 and Stage 3 from the patched source
with an isolated cache, run the focused core-parser regression, and only then
attempt the canonical Stage-4 command once.

Do not fall back to the removed Rust-hosted bundle. After a pure CLI candidate
passes admission, build the focused runner once and execute the calibration. A
PASS still requires runner SHA-256 plus distinct deliberate-fail and
zero-example exit-1 logs.

The currently deployed pure CLI is not an admissible test runner. Its ELF has
SHA-256 `04a38e21d6fbd86149d46d3ee2d761349f8ad29b02c5037a8eb589b6a1b9e4e0`;
both `test --help` and a focused interpreter run exit 139 before the runner
banner. GDB stops in `setenv`: `rt_env_set` receives value address `0x11` from
the recursion-depth update in `_CliMain.main`. The native interpolation of the
arithmetic expression produced a non-text value. Both the full CLI and the
lightweight test entry now pass `(depth + 1).to_text()` to `env_set`, with
source regressions for the two dispatch paths. This fix is pending the same
fresh Stage-2/Stage-3 rebuild required by the tuple-parser change; do not claim
the runner is runnable until the rebuilt candidate executes a focused spec.

## Patched compiler rebuild result (2026-07-16)

The isolated `build/bootstrap-font-runner-fresh-20260716` lane refreshed the
stale bootstrap-only Rust seed/runtime, then produced both pure-Simple compiler
stages with Cranelift; the wrapper reported its built-in sanity passed for each.
Stage 2 SHA-256 is
`36e6a0346ad006171b8dbb907c014703efda99b8a64b53b9e51b190ef16a95c0` and
Stage 3 SHA-256 is
`ecc01d7362da39cc84de15b1b2cab41e3d488ce4235939be4fdcffdcec06e3ae`.
Both symbol tables contain `parse_for_binding_names`, closing the prior stale
Stage-3 blocker. The first LLVM invocation was rejected because that seed did
not include the LLVM backend; the first Cranelift link exposed the stale
runtime's missing `rt_cranelift_new_aot_module_triple`, which the canonical
`--full-bootstrap` refresh supplied.

A retained direct parser probe cannot be admitted through the bootstrap-only
Stage 3: the removed `rust-hosted` bundle is rejected, while the supported
`core-c-bootstrap` mode fails closed unless the entry is
`src/app/cli/main.spl`. Do not weaken that production bootstrap guard for a
test. The focused parser regression therefore remains pending on a full
Stage-4 CLI that can execute `test`.

One direct Stage-4 attempt then used the exact canonical environment and the
verified Stage 3. A high-capability read-only review confirmed the command
matched `bootstrap_native_build_main`. It emitted a zero-byte log and no
candidate ELF, reached 35,635,608 KiB RSS at 6m54s, and exited 143 after roughly
13 minutes. No early-OOM journal entry identifies the signal owner, so retain
this as a bounded termination plus severe memory/observability evidence rather
than assigning an unsupported cause. Do not rerun Stage 2 or Stage 3; the next
lane should preserve their isolated cache and address Stage-4 peak memory and
phase telemetry before one further full-CLI attempt. Runner admission remains
pending.

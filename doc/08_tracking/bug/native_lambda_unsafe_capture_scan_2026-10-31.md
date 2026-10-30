# Unsafe blocks refused during native closure capture analysis

Status: confirmed source defect; native repair qualification pending.

The lockless-map boundary native test stopped at generated `describe` line
64:48 with `cannot materialize lambda for its declared function slot`.
Five declared cases executed zero assertions. The runner's one failed file
counter is not a successfully executed SSpec case.

The frozen input revision is `3e4dfcdce0d375dbe3c92ee63d891e84f70cc795`.
The pure-Simple producer is
`9633bf0af8b70d5f0324a35b244b3d08a62cdbcd1f8a3cd2aff246620f572dbd`.
The retained generated entry SHA-256 is
`39991d7c55e8d4c70f8bac1adb61aeb0d9777fda150dc49c1358294df9dd35a2`.

Evidence: `/tmp/incremental-runner-qualification-20261031/attempt4/specs/lockless-map-boundary-unit/`
contains stdout, stderr, preflight and the exact native invocation. The entry
is retained under that attempt's `source/test/native-generated--149909d9c9f1/`.

`UnsafeBlock` is a distinct HIR expression carrying a `HirBlock`. The three
closure walkers in `switch_operators_calls.spl` only traverse `Block`:
the capture predicate conservatively answers true, the supported-shape check
answers false, and the free-symbol collector omits the body. Therefore the
outer lambda refuses materialization before lowering any nested test.

The repair shares ordinary lexical block traversal with unsafe blocks in all
three walkers. It preserves capability lowering and all unknown-shape refusal
defaults. See [design](../../05_design/native_lambda_unsafe_capture_2026-10-31.md).
No test-body workaround or import-family change is authorized by this repair.

The reduced diagnostic under `/tmp/native-lambda-diagnostic-20261031/` confirms
the boundary without map or specification imports. `01b.compile.log` records
successful compilation of two nested `fn()` block callbacks. Its executable
ran once with empty output and exit 1, intentionally returning the asserted
callback count of one (`01b.run.log`). The counterpart wraps its counter update
and arithmetic assertion in `unsafe(capabilities: [ffi])`; `02.compile.log`
records the same MIR materialization failure at line 10:34. Separate caches
retain both attempts. The earlier `01.compile.log` is a distinct malformed
expression-body assignment diagnostic, not evidence for this bug.

Retest with an actual compiler containing the change, then run the unchanged
five-case lockless-map specification. Direct walker tests compiled as source
can independently verify those helpers on an older producer, but do not prove
that producer's own closure lowering has changed. A successful compiler link
or Hello sanity alone does not close this bug.

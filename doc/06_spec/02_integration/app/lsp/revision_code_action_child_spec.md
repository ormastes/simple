# Revision code-action child integration — authored manual

Execution/docgen NOT_RUN. Requires explicit SIMPLE_BINARY pointing to an admitted self-hosted runtime and a granted runtime slot. No seed or fake child fallback.

The first case creates a real workspace file with an ordinary TODO-format fix, synchronizes it into the canonical owner, calls the actual public codeAction handler/query child, and requires a version31 edit. The second runs a real Simple fixture emitting more than4MiB through the same canonical bounded runner and requires empty refused output/nonzero status. This does not claim memory/RSS measurement, other-platform qualification or execution before run receipts exist.

Pending invocation: SIMPLE_BINARY="$SIMPLE_BIN" SIMPLE_LIB=src "$SIMPLE_BIN" test test/02_integration/app/lsp/revision_code_action_child_spec.spl --mode=interpreter

Capture discrimination: the same binary/fixture first completes under9MiB with exact byte count/start/end markers and exit0. A direct canonical4MiB capture must complete with exit0 and exactly4194304 stdout bytes. The actual query wrapper then must return its reserved -10001 capture-ceiling code and empty output. Missing files, compile errors, crashes and timeouts cannot satisfy these controls. The three invocations test healthy fixture behavior, native transport ceiling, and wrapper rejection separately; none has run yet.

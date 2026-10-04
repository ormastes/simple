# Native generated-source snapshot lifecycle

Source: `test/02_integration/app/native_test_generated_snapshot_spec.spl`.
Status: one authored scenario, **UNRUN**; this companion is not a generated
execution receipt.

The scenario creates a unique real Git checkout under `build/test-artifacts`,
commits a tracked Simple source, and admits a cold `src`/`test` inventory.
The production staging helper then copies transformed source into an owned
`test/native-generated-*` directory. Canonical warm acquisition must discover
the untracked file, advance the inventory, and freeze its exact bytes. After
owned cleanup, warm acquisition must observe deletion while both earlier
snapshots retain their original bytes and manifest. The input source and the
caller's snapshot-root environment binding must remain unchanged.

No synthetic event, fabricated admission receipt, source-string inspection, or
manually edited inventory substitutes for real Git discovery. The isolated
fixture and immutable snapshots are retained for inspection. This test does
not execute the CLI refresh option, prove child environment isolation, or
qualify a native compiler; the backend integration and process tests must
establish those separate obligations.

With an admitted full CLI, set `SIMPLE_BINARY` to its absolute path and run:

```
<admitted-runtime> test test/02_integration/app/native_test_generated_snapshot_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose
```

Require the actual scenario verdict, invocation/source/artifact identities,
retained fixture, and qualified failing harness control. Compilation and exit
zero without executed examples are insufficient. See the generated-source
authority design and item4 native execution gate for remaining prerequisites.

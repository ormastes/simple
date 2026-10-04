# Native generated-source authority regression manual

Status: **UNRUN**. Manually authored companion to
`test/01_unit/lib/test_runner_native_source_authority_spec.spl`; not generated execution evidence.
Initial executable intent: `b83b2acb980`, preceding implementation. No observed RED/GREEN result.

The five scenarios call actual production owners. Run from the absolute checkout
root (including a linked worktree with its real `.git` file), with an admitted
self-hosted producer. Tests create uniquely owned temporary inputs and generated
`test/native-generated-*/entry.spl` files. They never create a fake authority receipt.

| Scenario | Independent assertion |
|---|---|
| Genuine spec transformation and staging | A real `input_spec.spl` is transformed by the native result wrapper; two staged files have exactly the transformed content, distinct directories, and non-discoverable `entry.spl` names. Keep retains files; cleanup leaves original inputs intact. |
| Coordinator request parsing | One refresh flag is consumed; remaining arguments retain order; absent flag means false; duplicate and worker refresh requests reject. |
| Invalid roots and inputs | Empty, relative, arbitrary temporary and file roots reject, as does a missing source under the real checkout. Original input content remains intact. |
| Cleanup ownership and retry | Forged or mismatched owners cannot delete an unrelated file. A real extra file obstructs nonrecursive directory cleanup; its bytes survive. Removing that obstruction allows retry. |
| Actual native compile argv | Refresh is requested with default source discovery; hardcoded `--source src/lib` is absent; backend, entry, runtime bundle, thread count and private cache remain. |

The existing `native_backend_contract_spec.spl` checks thread flag/value adjacency
instead of obsolete numeric positions. Its scenario count is unchanged.

Pending command after producer and generated-entry admission are available:
Set `SIMPLE_BINARY` to the exact same absolute admitted producer path before
invocation; child discovery must not fall back to a seed or another executable.
Retain verbose invocation receipts with the producer digest and actual argv.

```text
<admitted-runtime> test test/01_unit/lib/test_runner_native_source_authority_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose
<admitted-runtime> test test/01_unit/lib/nogc_sync_mut/test_runner/native_backend_contract_spec.spl --native-backend=llvm --sequential --no-cache --no-db --no-session-daemon --assert-ran --keep-artifacts --verbose
```

Require five executed scenarios, no failures and actual assertion evaluation for
the new suite. Instrumented scenario counts do not count individual assertions.
File/argv tests do not establish canonical snapshot publication, refresh ownership
across processes, successful native compilation, or execution of staged bodies.
Those remain real coordinator/worker end-to-end gates with exact producer,
generated-source and inventory provenance. No Rust seed fallback is authorized.

The existing `test/02_integration/app/test_runner_native_backend_spec.spl` now
uses genuine `*_spec.spl` passing/failing fixtures and a separate plain source
for the runtime zero-example rejection. Its positive fixture imports the real
app argument parser, exercising source discovery beyond std. Both LLVM and
Cranelift cases compare all eight parent source-authority environment bindings
before and after each child request without changing those bindings themselves.
These two scenarios remain UNRUN and do not require a preexisting parent snapshot;
the separate canonical inventory integration covers old/new snapshot bytes.

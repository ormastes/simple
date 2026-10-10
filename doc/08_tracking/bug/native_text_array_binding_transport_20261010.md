# Native typed text-array binding transport failure

Status: OPEN. The bounded repair lane exhausted three verification cycles. No repair is admitted.

The executable fixture is `test/fixtures/compiler/native_text_array_local/main.spl`. `TextScanner.source_chars` is `[text]`; `chars_match` reads an element into `val ch: text`, checks length, and compares `byte_at` values inside a while loop. Required output is `true\nfalse\n`.

## Pinned observations

- V15 source `480c13c90b6df728e00a45bece42efefaafe64d9`, producer SHA256 `05a2c618636246edb81d61f784bf05092b6b936db4d7982f1e5a76abdd5f9c57`: faithful fixture fails MIR with `byte_at receiver is not text`.
- V16 source `074f7a68ddbcb54864f502fdbec5ed7fb8977ea7`: declaration metadata publication inside scalar-copy branches does not fix it. GDB confirms the Let annotation remains Str, indexed initializer metadata is nominal, and the binding bypasses those branches.
- V17 source `bd1de0583466d59756b761f34ccf654298c02a37`, producer SHA256 `137bb5be916480b9d84377d0419ebf5b2cbf199e82111ae149a40fe94522e9cd`: declaration-aware routing and common metadata publication permit compilation/linking, but execution prints `false\nfalse\n`. This candidate is rejected.
- V17 passes the prior sixteen selected native controls and the negative nontext receiver criterion. These do not prove this fixture or full compiler correctness.

The rejected commits are `9414f4585` and `f433e1bea`. Recovery commit `0998b8494` restores MIR statement lowering from V15 while preserving new regression fixtures and release changes. Recovery native execution has not been repeated.

## Remaining investigation

Trace the indexed text element's value and owner metadata before binding. The GDB evidence proves an intact declaration and stale nominal initializer metadata; it does not prove that extracted runtime value is a correct text handle. Do not relax byte_at validation, retype arbitrary values, guess layouts, or treat compilation alone as success. Verify actual `true/false` execution and retain the nontext rejection gate.

WSL receipts are under `/home/ormastes/simple-linux-bootstrap-build-20261009/text-local-diagnostic-v16/text-local-gdb/` and `text-binding-owner-diagnostic-v17/final-focused-summary.json`. Published authorities, C40 runtime objects, logs, and immutable candidates are preserved; inactive caches have verified cold-archive restoration receipts.

# Native archive manifest validation blocks CAS publication

The Target 6 persisted archive fixture initially started a CAS transaction but aborted before the first `cas_put`. GDB showed `package_archive_manifest_v1` received an optional aggregate wrapper where it expected an entry and returned empty text. After explicitly unwrapping the aggregate, its digest validator still returned false for a valid 64-character lowercase SHA-256 digest; it compares one-character text values with native text relational operators. Other cache digest validators already use numeric `byte_at` checks because native text ordering can compare tagged addresses.

Correction to the earlier report: the raw `rt_file_create_excl` call returned `1`, and its Simple wrapper returned tagged `0xb`, which means **true**. File creation was not the failing step. The attempted wrapper changes were reverted without a commit.

The archive option bindings and byte checks moved execution to `cas_batch_stage_object_v1`, where GDB showed the compiler passed a null mutable reference. The function only reads the transaction, so its parameter now takes a value. CAS then rejected a mapping because a raw nullable file-read result was unwrapped as if it were a boxed Option; `cas_batch_read_v1` now normalizes that boundary to `Some(text)`.

The latest native spec reports **2 passes, 2 failures**. The graph and negative input examples pass. CAS now writes a generation file and `SEALED`, but no `batch-v1/CURRENT`; the positive publication and stale-payload examples still fail with `cold-publish-archive-generation-missing`. Inspect the lock/current-pointer branch next. The runner's zero exit status does not override its textual failure verdict.

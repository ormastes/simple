# Native archive manifest validation blocks CAS publication

The Target 6 persisted archive fixture starts a CAS transaction, but publication aborts before the first `cas_put`, leaving no `batch-v1/CURRENT`. GDB showed `package_archive_manifest_v1` received an optional aggregate wrapper where it expected an entry and returned empty text. After explicitly unwrapping the aggregate, its digest validator still returned false for a valid 64-character lowercase SHA-256 digest; it compares one-character text values with native text relational operators. Other cache digest validators already use numeric `byte_at` checks because native text ordering can compare tagged addresses.

Correction to the earlier report: the raw `rt_file_create_excl` call returned `1`, and its Simple wrapper returned tagged `0xb`, which means **true**. File creation was not the failing step. The attempted wrapper changes were reverted without a commit.

A local trial explicitly unwraps archive options and uses numeric byte checks in the archive and CAS validators. Its native build links, but the four-example spec executable exits 139 after about one second without a textual verdict. The trial remains uncommitted pending a crash backtrace and a bounded fix. Do not treat the previous 2/4 verdict as evidence for this changed binary.

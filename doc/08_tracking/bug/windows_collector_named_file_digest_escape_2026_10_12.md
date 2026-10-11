# Windows bounded collector rejects escaped named-file digest

Status: OPEN. Source-derived producer/consumer contract passes; native Windows Job launch remains unexecuted for this candidate.

Windows bootstrap run38174655243 at82bba686 built the seed/native_all and materialized55aliases without failures. C compiler probes then refused with collector helper hash mismatch and supervisor126/missingreceipt; no C compiler found was a downstream diagnosis. No compiler restart is used to investigate this precompile failure.

bootstrap_logged_windows_cargo hashes its helper using GNU sha256sum with a filename and takes the first output field. A path containing backslashes produces GNU escaped output whose first field starts with a backslash. The actual Python supervisor rejects that value because it requires64lowercasehex digits and independently hashes __file__. The original CI log did not retain the supplied digest, so this exact path cause remains pending native confirmation rather than inferred as proven from its terminal message alone.

The receipt log hash comparison used the same named-file rendering and could reject an otherwise matching receipt. Both hash sites now consume stdin. Hashing the same file through stdin avoids filename rendering while preserving byte-for-byte helper identity. The64hex and digest guard is unchanged. The source-derived regression executes the actual production assignment and the actual Python admission AST, without mocking its digest: named-path baseline rejects, stdin actualbytes admits, wrong/malformed digests reject, and CRLF changes are distinguished from authoredbytes while matching producer/consumer actualbytes admit. The actual production receipt-log comparison also admits matching log bytes and rejects changed bytes or malformed recorded digests. Native process launch and receipt publication are separate qualification still pending.

Evidence: /mnt/c/Temp/simple-windows-collector-path-hash-fix-20261012/{test-cycle2.log,source-receipt.json}; failedjoblog and retained compiler/archive authority under /mnt/c/Temp/simple-windows-bootstrap-integration-20261012. No full bootstrap or release PASS claimed.

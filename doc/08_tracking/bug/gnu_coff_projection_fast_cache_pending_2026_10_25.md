# GNU COFF runtime projection has no accepted fast cache path

Status: **OPEN / acceptance pending**. Functional first-miss projection is
verified separately; this is not a passed cache-performance or tamper test.

`llvm_runtime_owner_c_gnu_archive_v1` has a stable content key: ABI/profile,
resolved target, expected machine, archive content and ordered C object content.
Ephemeral `simple_rt_<PID>` paths are excluded; actual paths are validated
separately. Byte-identical objects at a new PID therefore share a content key.

The current helper still parses and recomputes the entire projection before a
cached output can be reused. For real DC022 this reads/mutates 109,939,334 bytes.
It deliberately compares against the source-rooted result so tampering of both
cached archive and local receipt cannot select a different output. This is
O(archive bytes), not a fast lookup. First-miss functional evidence is under
`C:/dev/simple-gnu-coff-owner-storage-20261025/diagnostic3`; the projection peak
was 404,356 KiB. A warm-hit time was not measured or claimed.

Follow-up design needs a trusted writer-owned immutable projection witness
within an admitted runtime authority, binding the stable input key to expected
output digest, or an efficient structural validation rooted in the original
archive. An ordinary local SDN receipt and its own hash do not supply that
authority. Existing MSVC size-only reuse is not an acceptable GNU oracle.

Acceptance must show: new-PID identical inputs hit the same content key; warm
reuse avoids full rewriting and has measured time/RSS; changed ordered object
content/target/profile misses; tampered output and jointly tampered output plus
receipt are refused; managed strict authority and original companions remain
bound. Preserve real first-miss/index/Rust-alias behavior and normal RSS limits.
No new authentication framework, unsafe shortcut or duplicate allowance is
silently introduced by the functional owner fix.

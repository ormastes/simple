# Native capsule fingerprint used a decimal text hash instead of SHA-256

Status: production fix built; canonical native Hello compilation and execution passed.

The Phase 2 compiler built on this host reached LLVM object emission, then
failed cold HIR object persistence with `cold-object-capsule-receipt-mismatch`.
Inventory counts were one typed receipt, one object path, one accepted capsule
identity, and zero objectless modules. This happened after the separate
source-inventory fixture-layout failure was repaired.

`FileFingerprint.content_hash` documents SHA-256, but `from_file` used
`incremental_hash_text(content).to_text()` whenever a text read succeeded.
That function returns the machine-word `rt_hash_text`, formatted as decimal.
Only a failed text read selected `rt_file_hash_sha256`. Core-C text reads
return complete binary bytes as text, so the native capsule writer used a
decimal hash while cold persistence independently compared SHA-256 of the
object bytes. A native C boundary probe confirmed a 659928-byte ELF file was
admitted as text and produced an 18-character decimal fingerprint; it cannot
equal the required 64-character SHA-256 value.

The repair hashes file bytes with `rt_file_hash_sha256` consistently and
retains nil for missing/unreadable inputs, plus the existing metadata reads.
Old text fingerprints invalidate once when compared against the new digest;
their decimal values are not accepted as authenticated object identities.
No cache identity is forced and no receipt comparison is weakened.

The existing cold object persistence probe now obtains the receipt digest
through the real `FileFingerprint` owner instead of inserting its independently
computed SHA directly. It covers a known text SHA, missing files, same-size
text changes, and an ELF-shaped byte sequence containing NUL and invalid UTF-8.
It compares the fingerprint with an independent byte digest and feeds the
writer-format receipt through actual cold object persistence and CAS readback.
The expanded probe's native build exited 1 before code generation. Its
830-file dependency closure exposed a separate Phase 2 flat AST bridge
failure: `unhandled decl node kind (tag=)`, first reported in
`driver_aot_native_output.spl:1:13`; HIR aggregate publication was blocked.
No probe executable was produced, so this focused regression remains unrun.
Its retained log is `build/item5-fingerprint-probe/build.log` in the isolated
WSL checkout. The canonical Hello result below remains a separate actual
compile-and-execute success; it does not stand in for this regression.

An independent check of the successful word32 native build verified the
production writer and cold CAS artifacts without recompiling or rerunning it.
The preserved ELF object is 11128 bytes and contains NUL bytes. Its capsule
receipt's byte count matches, and its digest equals independent SHA-256:
`73eca819b8b7f301578898ad29e13e2757fd135af23f206030188e98ce2c506e`.
The host-shared CAS blob at `objects/sha256/73/eca819b8b7f301578898ad29e13e2757fd135af23f206030188e98ce2c506e`
is byte-for-byte identical. The recorded native execution printed
`WORD32_NATIVE_PASS checks=4044`; it explicitly did not attest AVX512 execution.
The exact compiler identity, receipt/object/CAS paths and hashes, and native
executable hash are retained in
`build/item5-word32/fingerprint-capsule-verification.json` in the WSL checkout.
This verifies the repaired production receipt boundary; the additional
text/missing/same-size assertions in the expanded source probe remain unrun.

The corrected producer used release `f21317acc86ad9ada43023328173b9283fa9a24a`
and initial two-file patch SHA256
`9c9a9255887cede5ce6efec476f08f8291c37c7cde0c48a74bc0bcf55f65beaa`.
Three objects compiled and 1195 were reused; linking completed in 135.6 seconds
under the enforced 5859375 KiB limit, peak 1225868 KiB. Its SHA256 is
`b0fccf9f6667808acbb01bee6dbeaa53f3d0038e31068f9aeee58a21c6b4a53e`.
The later probe-only missing-file and same-size-edit assertions do not change
the producer implementation. This is not yet DB/web AVX512 or full-bootstrap
evidence. The final canonical Hello gate exited zero with `PASS — 2 case(s)
checked`: the entry arm compiled and executed the exact expected `hello`
output; the positional arm independently checked for crashes. The compiler
hash remained unchanged. The durable outer log is
`build/review/item5-linux-phase2-hello.log`; its result and compiler/runtime
identities are recorded in the isolated WSL checkout's
`build/item5-phase2/hello.result.json`.

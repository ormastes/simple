# Live process capture silently discarded output beyond 16MiB

Status: open pending actual P3 native execution of the regression fixture.

The Unix live process runner relays each newly appended chunk, then reads each
entire channel spool to return stdout/stderr. Its final read used the default
FileTextSession codec's 16MiB input budget. The compatibility API maps a typed
read error to empty text; the runner then deleted that spool. A successful child
could therefore print a publication receipt through the live relay while the
returned stderr omitted both the receipt and strict unresolved-symbol evidence.
The native-build coordinator correctly requires a receipt and consequently
reports failure despite the independently valid object.

For the 2026-10-25 focused constructor run, merged-log reconstruction establishes
more than 16MiB of known stderr trace rows and a stderr publication receipt. The
original redirected captures were deleted, so this is reconstructed attribution,
not recovery of the coordinator's returned capture values. The original raw
failure remains authoritative; independent manual linking is a separate proof.

The fix leaves the global codec budget intact. A private process-spool reader
captures the finite initial signed file size with reads of at most 1MiB. Strict
UTF8 decode may shorten a chunk by at most three trailing bytes; subsequent
reads revisit every byte. All raw extents and decoded byte lengths must match,
and final joined length and signed size must match the snapshot. Empty files
still receive a real one-byte EOF probe. This preserves CRLF, BOM, and NUL.
Memory remains proportional to complete output under the existing API contract.
The post-exit process-owned spool is assumed stable; size checks do not prove
immutability or protect against malicious same-size replacement.

Both channels are attempted. A failed capture retains its spool and returns an
explicit error with its path and nonzero result; timeout and relay diagnostics
remain visible. Successful channels retain their full text and delete only their
own successfully captured spools. The receipt and strict stub checks remain.

Validation: source review and git diff --check only so far. The native-required
process_capture_large_output_spec.spl fixture covers a 17MiB capture with final
receipt, 2/3/4-byte scalar splits, malformed UTF8, empty/missing files, byte-exact
BOM/CRLF/NUL, and nonzero worker status. No Phase2, runtime, or Rust rebuild was
performed. A future actual P3/native probe is required before marking this fixed.

@openbug: regression is not yet executed through the actual native owner.
@workaround: independently validating/linking an existing object is separate
provisional evidence and does not convert the original coordinator failure to PASS.

# Retained HIR re-scans all source receipts for each evicted module

Status: bounded source optimization independently reviewed; a real native
helper probe passed six cases and 210 counted contract checks. The authored
SSpec, retained-HIR integration and performance qualification remain pending.
Elapsed time and memory improvement remain UNMEASURED.

The retained low-memory HIR loop finds a module's immutable source receipt by
scanning all phase-1 rows, including resolver aliases. With N modules and R
receipt rows, that lookup performs N*R row visits even on HIR cache hits. A
1515-module/1515-row closure entails 2,295,225 receipt visits. The older fa967
producer and the 03e6d90af24 target both contain this loop. This operation
count does not attribute the previous 1800-second timeout or 7 GiB aggregate
peak to receipt lookup; actual phase measurements remain required.

The repair builds one frame-owned index of exact (path,module) identities
before the retained loop. Length-framed keys prevent concatenation ambiguity.
Duplicate exact rows retain an invalid sentinel permanently, including a third
occurrence; a zero hash and mismatched parallel-array lengths still fail
closed. A selected index continues to read byte length and hash from the
original immutable arrays. Missing witness diagnostics remain unchanged.

The actual selected core-C runtime uses FNV-1a text hashing and open-address
bucket lookup for Dict, not a linear vector scan: runtime_native.c
rt_core_dict_hash, rt_core_dict_lookup and rt_core_dict_has. The expected work
therefore becomes O(R+N) dictionary operations plus key bytes. This is expected
hash-table complexity, not a worst-case logarithmic guarantee. This patch does
not change the remaining alias/surface scans or claim the entire HIR phase is
linear. It introduces no broad scratch lifetime or new cache identity.

`source_receipt_index_spec.spl` covers alias positions, third duplicates, zero
hashes, malformed array shapes, pair-key ambiguity and comparison with the
original linear selector over a 98-row inventory. A genuine private two-file
Git project compiled a byte-identical copy of the index owner with these six
contracts in a small native main, using the actual `13d` compiler and selected
runtime. The exact run output was
`receipt-index-native-probe-ok cases=6 checks=210` followed by LF. Its collector
recorded native/raw exit 0 and its guard recorded measurement complete and
quiescent 1. This helper/provider result is separate from executing the SSpec
runner or the retained HIR call site.

Evidence identities:

- Probe Git revision: `583615f4d96c4428f73ed28b9e6058d928362a48`.
- Index-owner bytes: `14f885f366c446ce8035ca5d4a251b2a899ac3f477b16ed21e5284f83e4c9fdb`.
- Actual executable: `35f823689f83828bebf925e786173de97d0f0eaac3f3a515f5bdb06aad88447d`.
- Actual 49-byte stdout: `6cdef7984f1e2fda4007aec7e95740a0f01c9f5506ff6e5a58f221ff1bbcd41c`.
- Retained local evidence: `C:/dev/simple-receipt-index-native-probe-storage-20261025/attempt3/`.

The native run was an explicitly authorized diagnostic with RSS monitoring,
a finite timeout and observed host memory; it does not admit normal bootstrap
resource gates. Earlier harness-output collision and runtime-source locator
failures remain preserved. The successful compile was not repeated after a
post-runner helper-hash assertion: actual compiler/link receipts were observed
separately and the selected guard helper's cache key was proved from the same
pinned source/compiler/flags, with a different compiler-path spelling.

The full target must use this repaired source in a later rebuilt producer
before compiler performance can improve; building target source with the older
13d producer does not change that producer's own receipt lookup behavior.

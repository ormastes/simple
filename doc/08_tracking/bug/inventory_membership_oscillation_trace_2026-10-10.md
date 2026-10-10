# Inventory membership oscillation: opt-in transaction evidence

Status: diagnostic instrumentation; membership defect remains unresolved.

The same frozen checkout retained hash-valid inventory generations with counts
17153, 17245, 17153, 17245, and 17153. Exactly 92 materialized directory-alias
descendants were repeatedly added or removed; common source rows did not change.
The committed CURRENT record named the last generation and an empty untracked
membership blob. Snapshot identity changed, invalidating an unchanged module's
HIR key. Neither this change nor its tests establish the original cause.

The unchanged native porcelain parser and actual Git acquisition owner retained
all 92 paths in private tests. The complete refresh owner also preserved private
alias membership across cold/warm and alternating src/test requests. These
controls reject an unconditional parser or bare-array-push explanation. The
original executable's publication context remains unobserved.

## Diagnostic contract

Set `SIMPLE_INVENTORY_TRACE_ATTEMPT` to a unique 16–64 character lowercase
hexadecimal token per acquisition. The owner reads it once through the app
environment facade. The launcher must retain the executable, source and runtime
hashes separately; the token grants no cache authority. The explicit
`compiler_inventory_refresh_traced_v1` entry supports callers that already own
a request token. Reusing a token within one process makes attribution ambiguous.

At most four records, each at most 1024 bytes, describe BEGIN, OBSERVED, PREPARED
and RESULT. Records include PID, attempt, phase order, hashed root, family mask,
expected pointer, query status/count/byte count/hash, observed paths, reconciled
deletions, membership digest, and the returned publication generation. No raw
paths, source contents or Git output are printed. Counts unavailable without an
extra read are reported as `-1`; the old membership count is not reconstructed.

All output occurs after successful refresh-lock release. If unlock fails, no
record is emitted: absence is incomplete diagnostic evidence, never a PASS.
Malformed tokens produce a fixed rejection message after the ordinary refresh;
they do not reject or authorize the cache operation. Diagnostic records are not
part of CURRENT, inventory hashes, snapshot keys or admission decisions.

## Evidence and limits

- New criterion baseline: native complete refresh succeeded but emitted zero of
  four required records.
- Initial instrumented owner: 13 native cases passed, including enabled/disabled
  pointer parity, genuine deletion, malformed token, and recovery after a
  missing-cursor failure. These were not repeated after passing.
- Final owner: synchronized src/test acquisitions retained aliases and both new
  files. Unicode Git output reported the independent reader's 1882 bytes and
  SHA256. That Unicode refresh was rejected with `event-entry-invalid`; Unicode
  source admission is not claimed.
- A full inherited stderr pipe blocked the real native emitter after publication.
  An independent `LockFileEx` acquired the refresh lock before output was drained.
  Draining completed the child successfully.
- Replaying real records verified collector rejection of duplicate token/PID,
  truncated, malformed-token and over-cap evidence. This was collector replay,
  not a claim that the test invoked the same token twice in one native process.
- The SSpec diagnostic contract ran 2 examples, 2 passed, no skips or drops.

Native evidence uses a frozen bootstrap seed to compile the actual Simple owners
and canonical native runtime. It is not self-hosted compiler qualification. The
final two production owners match the tested bytes after newline normalization.
Required compiler/lib/MCP/LSP checks, self-hosted integration and an instrumented
deployed compiler remain open. No speedup, RSS nonregression for full builds, or
standalone changed-source-to-object 100 ms target is claimed.

Local evidence packet: `build/inventory-publication-trace-20261010/`, containing
`baseline-oracle.json`, `publication-native-result.json`,
`remaining-native-result.json`, source hashes and closed process-tree receipts.
Use these records to identify the first divergent boundary before repairing
membership logic; do not weaken Git scope, hashes or cache keys.

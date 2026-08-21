# Verification report: SimpleOS complete OS hardening

Date: 2026-08-20

## Outcome

`STATUS: FAIL`

The bounded continuations added substantial fail-closed source foundations,
but the umbrella feature is not release-ready. No admitted self-hosted Simple
executable was available, so no runtime, QEMU, physical-board, performance,
fuzz, soak, or doc-generation evidence was accepted.

## Passing static gates

- `git diff --check` produced no errors.
- Working and staged direct-environment runtime guards passed.
- `doc/06_spec` contains no executable `*_spec.spl` files.
- Focused final-review surfaces contain no newly accepted placeholder or
  source-introspection evidence. The umbrella traceability helpers no longer
  use unconditional placeholder failures: every REQ/NFR is bound to an
  existing executable acceptance owner and exact expected receipt path, the
  production capability-ledger validator checks the complete `Blocked`
  candidate, and the helper then emits `BLOCKED[...]` so it cannot count as
  acceptance. The detached live-SSH predicate test is explicitly rejected as
  false-green below.
- New/refactored owner files are below 800 lines. The former 1,420-line SSH
  session and 1,778-line NVMe operations owners are now cohesive split modules;
  the live SSH session is below 800 lines and the largest NVMe split owner is
  below the same ceiling.
- The staged numbered-artifact guard passed.

The working numbered-artifact guard failed on the unrelated untracked
`.claude/worktrees.pre_migrate_backup/` tree. It was preserved as concurrent
user/agent work.

The mission-critical prerequisite gate reported `STATUS: PASS` with no missing
host prerequisites. The mandatory release gate produced no output or terminal
status for 90 seconds and was stopped under the no-runaway rule; it is not
accepted as evidence and cannot yield release `PASS`.

## Closed static defects in the latest continuation

1. HTTP worker/TLS split symbols now have explicit minimal public or
   package-only boundaries, including the canonical TLS-common provider.
2. QUIC uses the exported nullable CSPRNG facade and keeps connection-ID
   admission fail-closed.
3. Disk-image role paths and every public renderer field are revalidated before
   canonical SDN emission.
4. `sha256sum`/`md5sum` no longer emit a DJB2 placeholder: they use the
   pure-Simple cryptographic owners through a bounded VFS read/close path and
   known-answer specs. The primary-tool row remains `Blocked`, not supported.

The first independent bounded static review returned `FAIL` and named exact
serialization, SFTP value-copy, per-socket read, traceability, matcher, and
documentation defects. Those findings were corrected in the working tree; a
fresh independent recheck is required before this report may record a static
PASS. Executable specs were not run.

## Latest source-static continuation

- HTTP and DBD share one bounded mutable fixed-ring TLS application-record
  owner, accept split/coalesced records, and advance receive sequences only
  after authenticated token/count commit. One-byte fragmentation has exact
  linear byte-work evidence; HTTP remove/mutate/reinsert and DBD direct-owner
  mutation avoid value/COW copies of the ring.
- DBFS now has dual checksummed namespace slots, append-only checksummed blobs,
  rollback on failed persistence, and a real `BlockDevice.flush()` durability
  boundary on audited hosted mutex providers. SimpleOS device registration
  remains `Unsupported` because its `spl_mutex_*` provider is a no-op and no
  atomic-CAS/scheduler-exclusion owner exists; physical Flush-backed restart
  evidence therefore remains absent.
- An OS-layer NVMe adapter binds a mutex-owned process generation token to the
  current trusted PCI/controller/namespace incarnation and validates it per
  operation. Durable I/O still returns `ResetNotSerialized` because controller
  reset and queue I/O do not share one lifecycle lock; no filesystem capability
  is promoted.
- SSH live AES-GCM receive now resolves the exact socket owner and validates a
  typed `4 + packet_length + 16` plan before reading the body, with a maximum
  total of 35,020 bytes. Live SFTP subsystem routing uses one mutable bounded
  ring owner with linear drain work. WM owns deterministic focus
  and bounded damage state. The dedicated REQ-017 system spec now exercises
  focus/stacking, close fallback, bounded damage, focused input routing,
  composited overlap pixels, and restart fencing through production owners.
  Its separate live-guest scenario invokes the canonical QEMU wrapper and
  requires input-to-scene/presentation correlation plus four hash-addressed
  QMP frames; it reports `BLOCKED[REQ-017-LIVE-GUEST]` rather than promoting
  host pixels when the admitted runtime or guest capture is unavailable.
  Checksum, grep, and ps have canonical filesystem
  package/launcher identities but return 126 without admitted artifacts and
  loader tokens.
- The installer admits executable package bytes only through canonical ELF or
  SMF-with-embedded-ELF validation, rejects bootstrap seed provenance, and emits
  blocked rows instead of fabricating absent tools/libraries. Host file-read
  TOCTOU remains open because no bounded read facade exists.
- The privileged loader consumer re-reads and hashes the retained handle,
  rebuilds the process image, and can map/reclaim a bounded x86_64 address space;
  the scheduler-owned adoption seam now publishes each authenticated execution
  exactly once and returns successful transactions to reusable `Idle`, while
  replay or indeterminate failure remains quarantined. Receipts remain
  non-authorizing because production cryptographic token issuance and admitted
  runtime evidence are still unavailable. ARM/RISC-V mapping is fail-closed.
- Toolchain status now performs bounded ELF admission and never reports a
  present placeholder as READY. The current `clang_static` payload is 16 KiB
  of zero bytes; LLVM cross/sysroot artifacts are absent.
- Evidence admission now re-hashes bounded source/image/binary/config/fixture
  and ordered artifact bytes, carries exact per-sample RSS and the complete
  verified artifact set into performance admission, and commits handle spend,
  admission expiry, and the canonical ledger under one mutex. Every unlock is
  checked; indeterminate completion quarantines the owner and exposes no success
  handle or ledger payload while retaining mutation to prevent replay. Crypto PASS is
  still disabled: the repaired common Ed25519 owner has no authoritative
  self-hosted executable KAT/native constant-work receipt.

The deployed release binary identifies itself as a Rust bootstrap seed and was
therefore not used. These additions have static checks only. The prior
independent bounded review was performed before the final safety/performance
corrections and returned `FAIL`; a fresh independent re-review is still required
before any independent static `PASS` may be recorded.

## Remaining release blockers

The selected umbrella requirements remain blocked on cryptographic token
issuance plus executable scheduler-adoption evidence, durable target device
Flush/FUA serialization, target-native Simple/LLVM
artifacts, filesystem-resident primary-tool artifacts and receipts, complete
HTTP/2/HTTP/3/QUIC-TLS, DB/RESP-TLS, and SSH profiles, production WM visual
capture, and every required x86_64/AArch64/RV64GC runtime/hardware campaign.
The WM host-fixture scenarios are supporting behavioral evidence only; the
live x86_64 wrapper was not executed in this verification wave because no
admitted self-hosted SSpec runtime was available, and the AArch64, RV64GC,
native-host, and physical-board visual rows remain open.
Installer descriptor-bound no-follow reads, target Simple/LLVM artifacts,
SimpleOS atomic scheduler/device serialization, and executable runtime evidence
remain explicit blockers. Closed items—live SSH framing/SFTP reachability,
shared TLS/SFTP fragmented-ingress complexity, and the two oversized owners—do
not remain on the blocker list.

## 2026-08-21 follow-up: gate repairs (status still honest FAIL)

1. Traceability is no longer unconditional. `_propagate_blocked` in
   `test/helpers/simpleos_complete_os_hardening_steps.spl` now consults the
   real expected receipt path: absent receipt reports
   `reason=receipt-absent`, a present receipt reports
   `reason=receipt-present-but-admission-unavailable` with the production
   blocker (`cryptographic-verifier-unavailable`, capability_ledger.spl).
   Neither path can silently pass.
2. The mandatory release gate no longer ignores the umbrella bindings. New lane
   `scripts/check/check-simpleos-umbrella-traceability.shs` (self-test first and
   fatal, verdict line last) checks every `# @req` id is bound, every bound
   acceptance owner file exists, and every requirement's receipt presence.
   `check-simpleos-mission-critical-release.shs` fails when that lane is not
   PASS; its self-test gained a must-FAIL fixture for a red lane.
   Current honest verdict: `FAIL — 34 binding(s) checked, 34 BLOCKED
   (receipt-absent), 0 unbound, 0 missing owners`.
3. The numbered-artifact guard classifies nested agent worktree copies
   (`.claude/worktrees*/`) out of scope in the guard itself instead of relying
   on a local `.git/info/exclude` entry, and now emits PASS/FAIL/ERROR verdict
   lines with a classified-path count. Working copy: `PASS — 416 path(s)
   classified in --working, 0 numbered artifacts`.

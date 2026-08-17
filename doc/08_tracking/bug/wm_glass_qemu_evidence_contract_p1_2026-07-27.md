# WM Glass QEMU Evidence Contract P1 Gaps

**Status:** open / fail-closed
**Isolated reviewed base:** `a296e5f5a6`
**Affected rows:** `FR-WM-GLASS-X86-QEMU-0001`,
`FR-WM-GLASS-ARM-QEMU-0001`

The canonical x86_64 and ARM64 desktop entries install the generated Aetheric
theme before compositor and first-frame construction. ARM also has substantial
frozen-source, NEON parity, QMP/VirtIO, frame, RAMFB, and artifact-rehash
validation. Those facts do not yet admit either live row.

## Committed-source blockers

1. The x86 wrapper hashes mutable source inputs but does not bind them to a
   clean Git revision and published frozen-source manifest. An explicitly
   supplied external ELF can still run without a kernel-admission receipt.
2. The x86 guest emits positive SSE2 counters, but the wrapper does not require
   the receipt or prove bit-exact parity with an independently computed scalar
   oracle.
3. The x86 wrapper matches IRQ, WM-state, and frame identifiers by existence
   rather than strict serial order, and it has no correlated damage receipt.
4. The ARM direct-`-kernel` route has firmware identity marked N/A, but it does
   not validate guest theme identity, material mode, selected backend, or
   fallback status.
5. Neither row retains first-themed-frame timing and QEMU maximum RSS required
   by the selected NFRs.

## Sibling-work review

Active sibling-owned uncommitted changes add useful x86 SSE2 parsing, separate
QMP make/break, richer click/text/control/drag receipts, framebuffer
comparisons, queued-pointer drain, and expanded ARM correlations. They are not
admissible yet:

- the x86 lane begins frozen admission but does not publish or consume the
  resulting manifest, leaving the external-ELF bypass open;
- the ARM event receipt marks focus from transport readiness and finalizes
  before WM processing and frame commit, so the checker can accept a synthetic
  or prematurely ordered receipt;
- source-string contracts cannot replace retained live artifacts.

Do not copy or commit those dirty files from another session. Re-review only
after their owner commits a scoped change.

## 2026-07-27 bounded repair hard stop

A clean isolated lane attempted three frozen-admission repair cycles. The first
two candidates were independently rejected because caller-authored receipts,
mutable source/tool paths, pathname reopen races, unbound final boot artifacts,
unhashed run manifests, and helper-only fake-QEMU tests could still produce
false evidence. Neither rejected commit was integrated.

The third cycle moved regular artifacts toward private no-follow snapshots and
unlinked inherited descriptors, made x86 fail closed pending a raw immutable
ESP-image builder, and added production-wrapper behavior modes. Its single
permitted final gate stopped immediately on macOS:

```text
check-simpleos-wm-fullscreen-evidence.shs: line 16: /dev/fd/7: Permission denied
```

This attempted execution of the unlinked fake-QEMU snapshot through macOS
`/dev/fd/7` was denied. The lane reached its hard iteration cap, so the final
edits remain uncommitted in
`/private/tmp/simple-wm-qemu-frozen-repair2-20260727` over rejected commit
`6108a099f5`; they are not source evidence and must not be absorbed. No fourth
attempt, live QEMU, bootstrap, integration, or push ran. A fresh lane requires:

1. a reviewed host C launcher that executes a verified private QEMU path
   snapshot with `posix_spawn`, preserves only fixed media descriptors through
   QEMU fdsets, supervises the process to exit, and truthfully limits its
   threat claim to race resistance for honest same-UID concurrency;
2. a builder that emits one raw immutable x86 ESP image rather than a mutable
   vvfat directory;
3. production-wrapper fake-builder/fake-QEMU behavior tests proving exact
   descriptor-backed launch and negative launch absence after every tamper;
4. hashed, inode/size/hash-revalidated run manifests before and after execution.

Darwin SDK research found no `fexecve` or `execveat`. A subsequent isolated
host-C helper lane therefore used the `posix_spawn` direction. Cycle 1 was
independently rejected for a broken public export, caller-controlled descriptor
collisions, noncanonical pre-spawn receipts, inaccurate build provenance, an
unwired/dead raw profile, and source-string-only tests. Cycle 2 repaired fixed
roles/FDs, canonical argv/environment framing, and normal catalog
compatibility, but retained P0 gaps. The final cycle stopped without weakening
those gates. Candidate `e98275fca0` remains unintegrated because it lacks:

- supervised process-group lifecycle, signal relay, wait/status policy, and
  post-exit atomic receipts;
- pre-spawn environment validation and exclusive receipt reservation, with
  kill-and-wait cleanup on every post-spawn failure so no child is orphaned;
- QEMU code-signature plus recursive dylib/resource closure admission;
- truthful helper-build provenance: no-follow source snapshot, exact compiled
  snapshot/argv/sanitized environment, compiler+SDK closure, verified
  compiler/helper signatures, helper dylib/resource closure, and unique
  concurrency-safe output/receipt publication;
- supported evidence-wrapper construction and validation of exact
  `-add-fd`/`/dev/fdset` roles;
- a structurally isolated BOOTX64/kernel-only `wm-uefi-boot-v1` producer; and
- executable fake-QEMU behavior tests rather than source-substring inspection.

No QEMU guest, bootstrap, integration, or push ran in that helper lane. The
candidate and its known unstaged Gradle EOL checkout noise are not evidence.
Future snapshots and receipts must also be reopened and rehashed after `fsync`,
then atomically published with their containing directories synced.

## 2026-07-27 BRR2 foundation review hard stop

A separate clean lane attempted three bounded source-only cycles for a canonical
BRR2 guest receipt, host parser, normalized SimpleOS lifecycle model, and
focused specifications. Commits `a2e949d838`, `2edbe367ed`, and `c10eff40a9`
remain isolated and unintegrated. No runtime test, QEMU launch, bootstrap, Rust
seed, or push ran.

The final review confirmed that the numeric no-allocation guest owner, fixed
big-endian lengths, boot/source splice binding, nonzero source identity, BRR1
compatibility, bounded geometry, raw-wire parsing, and separation of the
four-stage SimpleOS lifecycle from the legacy six-native-event aggregate were
statically sound. It still rejected the series at the mandatory third-cycle
cap:

1. the public lifecycle normalizer collapses exact parser failures to
   `invalid_brr2_receipt`, so capture validation cannot surface
   `checksum-mismatch`, `unknown-endian`, input-sequence mismatch,
   rendered-revision mismatch, or nonmonotonic-event-time as its changed system
   scenario requires; and
2. the selected four-backend requirement and detail design still require the
   legacy six-event sequence for every target, contradicting the truthful
   SimpleOS four-stage lifecycle contract and leaving requirement coverage
   stale.

A fresh lane must first resolve the product contract: either amend the selected
requirement/design so SimpleOS proves its distinct IRQ -> WM -> damage ->
present lifecycle without claiming six native event kinds, or extend the wire
protocol with independently correlated event-kind receipts. It must then
preserve exact parser reasons through the public capture boundary, update the
system scenario/manual together, and obtain independent high-capability review.
The rejected three-commit series is not a base to cherry-pick piecemeal and is
not live evidence.

## Required repair and resume

- Publish and consume the x86 frozen manifest; reject every external kernel or
  disk that is not bound to it.
- Provide the reviewed supervised `posix_spawn`/fdset helper and raw immutable
  x86 ESP-image builder required by the bounded hard stops above.
- Bind the helper build to the exact no-follow source snapshot, actual
  compiler/SDK closure, canonical argv/sanitized environment, verified
  signatures/dependencies, and concurrency-safe output/receipt publication.
- Resolve the BRR2 requirement/design mismatch and preserve exact parser
  failure reasons through the public SimpleOS capture boundary before using
  BRR2 as event/order evidence.
- Require x86 SSE2 execution and bit-exact scalar parity.
- Require strict QMP input -> guest IRQ/VirtIO -> WM state -> damage -> frame
  commit order, with the event receipt finalized only after the correlated
  frame.
- Bind ARM theme/material/backend/fallback identities; firmware remains N/A
  for the direct-`-kernel` route.
- Retain first-themed-frame timing and QEMU max RSS for both rows.
- Preserve independent `pmemsave`/RAMFB captures and rehash every artifact
  before admission.

After an admitted source-matched artifact set exists, resume with:

```sh
BUILD_DIR=build/simpleos_wm_fullscreen_evidence \
SIMPLE_BIN=/absolute/path/to/admitted/simple \
sh scripts/check/check-simpleos-wm-fullscreen-evidence.shs

sh scripts/check/build-simpleos-arm64-desktop-engine2d-attested.shs
sh scripts/check/check-simpleos-arm64-qmp-input-evidence.shs
```

No bootstrap, Rust seed, stale artifact, direct-kernel shortcut, source-only
contract, or screenshot alone may close either row.

## Re-verification 2026-08-17

Read the full doc. This is a process/evidence-contract gap doc (frozen-source
manifests, kernel-admission receipts, parity oracles, strict-ordering
correlation, timing/RSS retention for two FR-WM-GLASS QEMU rows) rather than a
single code defect with a clear file:line fix. The listed "Committed-source
blockers" are architectural evidence-contract gaps spanning the x86/ARM QEMU
wrapper scripts and guard (`scripts/check/check-simpleos-wm-fullscreen-evidence.shs`,
in scope) plus guest-side kernel/compositor code (out of scope). No single
narrow patch closes either FR-WM-GLASS row; doing so would require the frozen
admission manifest + receipt plumbing described in the doc's "bounded repair
hard stop" section, which is multi-file, cross-lane work already tracked as
its own bounded-repair effort.

**Classification: SKIPPED-CLAIMED (documentation/process gap, not directly
patchable in this pass).** Verified the doc's own framing is still accurate
by re-reading `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`'s
overall shape; no code or doc content changes made beyond this
re-verification note. Status remains open / fail-closed as recorded.

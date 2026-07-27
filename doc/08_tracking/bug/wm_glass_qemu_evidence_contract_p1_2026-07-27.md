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

1. a reviewed `fexecve`/equivalent helper that executes an already-open
   authenticated tool descriptor without reopening a mutable pathname;
2. a builder that emits one raw immutable x86 ESP image rather than a mutable
   vvfat directory;
3. production-wrapper fake-builder/fake-QEMU behavior tests proving exact
   descriptor-backed launch and negative launch absence after every tamper;
4. hashed, inode/size/hash-revalidated run manifests before and after execution.

## Required repair and resume

- Publish and consume the x86 frozen manifest; reject every external kernel or
  disk that is not bound to it.
- Provide the reviewed descriptor-exec helper and raw immutable x86 ESP-image
  builder required by the bounded hard stop above.
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

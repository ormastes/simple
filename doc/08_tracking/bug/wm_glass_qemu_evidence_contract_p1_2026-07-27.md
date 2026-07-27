# WM Glass QEMU Evidence Contract P1 Gaps

**Status:** open / fail-closed
**Reviewed base:** `origin/main` through `15fad441d7`
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
4. The ARM wrapper does not retain firmware identity/hash and does not validate
   the guest theme identity, material mode, selected backend, or fallback
   status.
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

## Required repair and resume

- Publish and consume the x86 frozen manifest; reject every external kernel or
  disk that is not bound to it.
- Require x86 SSE2 execution and bit-exact scalar parity.
- Require strict QMP input -> guest IRQ/VirtIO -> WM state -> damage -> frame
  commit order, with the event receipt finalized only after the correlated
  frame.
- Bind ARM firmware plus theme/material/backend/fallback identities.
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

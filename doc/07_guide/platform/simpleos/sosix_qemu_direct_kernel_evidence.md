# Direct-kernel SOSIX QEMU evidence

Use schema v2 for QEMU guests launched with `-bios none`. Do not invent a
firmware binary. Supply `none` for firmware path/id/version, use mode
`direct-kernel`, and require the single firmware-stage marker `guest-entry`.

The kernel must print literal `guest-entry` before the unique run nonce. Host
admission must be captured before launch. A historical transcript lacking that
event or pre-run admission cannot be upgraded post hoc; run the guest again.

External UEFI, OpenSBI, and board-ROM rows keep real firmware files, hashes,
versions, and their existing entry/handoff/guest-entry stage sequences.

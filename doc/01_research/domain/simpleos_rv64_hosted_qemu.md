<!-- codex-impl -->
# SimpleOS RV64 Hosted QEMU Domain Research

- QEMU `virt` on RV64 commonly exposes host reachability through `-netdev user,...,hostfwd=...` paired with a VirtIO NIC. That is enough for a truthful host-side SSH/HTTP probe lane.
- Staged OS bring-up benefits from explicit preflight versus acceptance phases: preflight proves machine shape, disk attachment, and forwarded network plumbing; acceptance additionally requires guest services and disk-backed process execution.
- Synthetic smoke markers are useful only if they are labeled as smoke. Reusing hosted or process-backed wording before the kernel owns those paths weakens verification.

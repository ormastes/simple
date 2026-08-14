# SOSIX QEMU remaining-owner NFRs

- `NFR-SOSIX-QEMU-BOUND-001`: Every process used by the system spec has an
  explicit timeout; a timeout, signal, or nonzero unexpected exit fails closed.
- `NFR-SOSIX-QEMU-PROV-001`: PASS evidence is producer-generated and bound to
  admitted runtime, host, QEMU, media, source, and workload identities.
- `NFR-SOSIX-QEMU-ISO-001`: Immutable source media is never mutated through a
  direct path, normalized alias, or symlink alias.
- `NFR-SOSIX-QEMU-DOC-001`: The executable SSpec is the manual source; only
  zero-stub `spipe-docgen` output may populate `doc/06_spec`.
- `NFR-SOSIX-QEMU-CONVERGE-001`: Each acceptance gate runs at most once per
  verification cycle, with no more than three fix cycles.

# Bootstrap product work-volume disk guard

REQ-DISK-001: Apply the unchanged 4 GiB/6 GiB thresholds to the filesystem owning product bulk writes. REQ-DISK-002: New fallback storage roots must be fresh physical children of that checked job root, rejecting existing directories and ordinary/dangling symlinks before writes.

The original external product owner rejected an ample owned work volume because unrelated `/` had only 360828 KiB free. Sources, objects, private Git metadata and scratch are job-owned. The fix checks that volume and binds TMPDIR and normal user/worktree storage owners to fresh job children. Previous caller storage overrides are intentionally replaced for this isolated product transaction.

Evidence: policy controls11 retained in `product-work-volume-controls.Vl2XTC`; top-level symlink negative1 in `product-work-volume-controls.6HYcwL`; actual df old/fixed threshold comparisons4 in `product-disk-work-volume-real-boundary-result-20261008`. Normal production preflight uses actual admitted80fa/source2aee/tool authority and stops after guard/storage binding at inventory regeneration; its normal outer exit1 is not product success. New child-storage regression evidence is retained separately.

Changed-owner controls cover both thresholds, low space, same filesystem, df error/malformed/missing report, missing job root and symlinks. Provider input/output/cache usage and comparable cohort ratios are unavailable. This narrow shell-boundary verification does not qualify full compiler products, memory limits or Phase2. SHS executable controls are source-bound; there are no SPL BDD scenarios or generated SSpec manuals to mirror in this change.

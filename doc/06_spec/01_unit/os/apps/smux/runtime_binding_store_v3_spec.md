# Immutable runtime binding artifacts

Status: **AUTHORED_UNRUN**. Real temporary filesystem operations are authored but unexecuted. Stored synthetic metadata is not host admission, helper ownership, provider attachment, or capacity release evidence.

Source: `test/01_unit/os/apps/smux/runtime_binding_store_v3_spec.spl`.

Prerequisites: hosted temporary filesystem, secure temporary directory creation, regular-file no-follow reads, exclusive writes, mode 0600 support, atomic no-replace publication, file and directory synchronization, and recursive fixture removal. Missing support fails the scenario; no fallback or skip is provided.

1. Create a real private temporary root and preserve the first immutable request and plan. Identical replay succeeds; changed target revision, plan digest, and request replay fail without replacing retained bytes.
2. Publish real receipt bytes once without treating stored metadata as current runtime facts. The first receipt is immutable; changed receipt bytes and a foreign common plan digest fail.

Production storage still requires the sole protected HostLocalRoot journal owner. No-replace publication additionally prevents overwrite if a competing writer appears between existence check and publication. Later inspection derives current cleanup and settlement facts instead of overwriting the first receipt. Cleanup locator/recovery functions are outside these scenarios.

Each scenario removes its private root before checking captured results. A failure before root creation is a failed backend precondition, never positive evidence.

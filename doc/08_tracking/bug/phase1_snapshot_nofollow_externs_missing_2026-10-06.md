# Phase1 snapshot no-follow externs missing

The Linux seed sweep reached native_build_numbered_closure_spec.spl and failed with unknown extern rt_snapshot_symlink_create_nofollow_v1. Registration-level checks also reproduced missing link-match and readonly providers. The native C runtime already implements all three operations.

Provide Unix interpreter implementations with the same path and target constraints, exclusive symlinkat creation, exact readlinkat readback, no-follow final target validation, and descriptor-based readonly sealing. Reuse the existing safe_artifact_open_root directory walker for every ancestor. OwnedFd releases descriptors on all exits. Readonly opens use O_NONBLOCK as well as O_NOFOLLOW, so an unsupported FIFO cannot block before the kind check.

Three parsed-Simple regressions failed before registration and passed after repair. They verify exclusive creation, exact raw target, symlink chains, confined parent targets, escape and malformed-target rejection, wrong kinds, symlink ancestors, and readonly mode bits on files and directories. One Rust expression compile error was corrected before the successful run. Enforcing RSS evidence records exit 0, quiescent 1, peak 4831592 KiB, and maximum sample gap 3038 ms. Evidence is retained under /tmp/simple-snapshot-links-repair.

These interpreter registrations are Unix-only; Windows remains outside this Linux repair and requires its own provider. The original numbered-closure spec requires verification with a newly built seed. Whole seed qualification and subsequent phases remain pending.

# Windows C authority ownership

- Selection/CMake/Cargo/native evidence and merge owner: /root/windows_longpath_review.
- Bounded lint provider, registry, SSpec and manual author: /root/windows_msvc_toolchain.
- Independent workflow fix: /root/windows_ci_failures, PR1216; no overlapping workflow edits.
- Final source reviewer: /root/windows_longpath_review, gpt-6-astra/xhigh. Any high-severity finding blocks publication until corrected.
- Bootstrap execution/admission: /root/bootstrap_stage2_sol and root coordinator.

Lint author changes require review of selection parsing, path scope, canonical registration and current-source cases. The absence of a self-hosted runner remains an explicit verification gap.

# Host managed journal cleanup

Approved finite ownership scope; authored / NOT_RUN.

- **HOST-OWNER-CLEANUP-01:** Managed host capacity open must preserve canonical cleanup capability through journal acquisition, replay, projection and recovery errors; only actual replay success may yield a capacity owner. Existing charged/released evidence projection remains authoritative.
- **HOST-OWNER-CLEANUP-02:** Managed root/finite-command close must retain canonical cleanup plus explicit native release state through all errors. Cleanup success is not workload success. Unknown is quarantined; stale tokens cannot affect replacements; consumed errors never become successful closure.
- **HOST-OWNER-CLEANUP-03:** Incomplete root acquires no writer. Finite native runtime must refuse non-Linux hosts before POSIX privacy checks; Windows persistent ownership requires its reviewed native capability, not a backend fallback.

See `doc/05_design/host_owned_journal_v2.md` and the authored SSpec manual for exact caller migrations and unexecuted platform/fault evidence. No runtime qualification or power-loss durability is claimed.

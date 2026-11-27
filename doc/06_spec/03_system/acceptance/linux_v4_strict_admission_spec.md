# Linux V4 unsupported strict admission

`test/03_system/acceptance/linux_v4_strict_admission_spec.spl` runs the native
Linux host selfchecks. The V4 admission matrix rejects group and tree policies,
and cgroup memory enforcement for each descendant policy, before executable
acquisition. It checks the admission error and absence of a process or ticket.
The lifecycle selfcheck also runs. The wrapper exits 77 on non-Linux hosts;
that is unavailable evidence, not a pass. This test does not establish a
protected cgroup boundary or qualify strict descendant or memory ownership.

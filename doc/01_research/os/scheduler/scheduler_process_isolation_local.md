<!-- codex-research -->
# Domain Research: Scheduler + Process Isolation

Date: 2026-04-20

## References

- Linux EEVDF documentation: `https://www.kernel.org/doc/html/latest/scheduler/sched-eevdf.html`
- Linux deadline scheduler documentation: `https://www.kernel.org/doc/html/latest/scheduler/sched-deadline.html`
- Linux cpuset/scheduler-domain load balancing: `https://docs.kernel.org/5.15/admin-guide/cgroup-v1/cpusets.html`
- FreeBSD ULE scheduler man page: `https://man.freebsd.org/cgi/man.cgi?query=sched_ule&sektion=4`

## Findings

- EEVDF keeps fairness with virtual runtime/lag while favoring eligible tasks with earlier virtual deadlines, which fits SimpleOS interactive/fair defaults.
- Linux deadline scheduling combines EDF with CBS and admission control; without admission, deadline promises are unsafe.
- Modern SMP schedulers use per-CPU run queues plus topology-aware load balancing instead of one global queue.
- FreeBSD ULE validates the same direction for SMP/interactivity: CPU affinity, per-CPU queues, and interactivity-aware policy.

## V1 Recommendation

Implement per-CPU run queues and fair/background policy now. Carry RT/deadline metadata through the stack, but reject deadline activation until EDF/CBS admission and bandwidth isolation are present.

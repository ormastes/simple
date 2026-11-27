# Linux BuildRunner cgroup containment

Authored scenario manual; native C checks executed, SSpec wrapper not executed.

1. Use an isolated Linux cgroup-v2 namespace with memory already delegated.
   Run `sh scripts/check/check-linux-capacity-containment.shs`; missing delegation
   is an error, not a successful skipped test.
2. Observe a descendant creating a new session after fork. Require a live pidfd
   before retirement and require the owner to kill it after its original
   leader exits. The harness subreaper then reaps the descendant; the owner
   reaps the leader and releases the exact cgroup parent.
3. Touch more memory than the child cap. Require a kernel OOM counter, SIGKILL
   exit status, empty tree, and cleanup. A timeout or manual cancellation does
   not satisfy this scenario.

The native run passed both scenarios. Disabling the cap in a temporary negative
control failed the memory assertion. Neither result qualifies the Simple ABI or
the complete BuildRunner command. See the linked
[evidence](../../../../08_tracking/bug/buildrunner_linux_containment_evidence_2026_10_29.md).

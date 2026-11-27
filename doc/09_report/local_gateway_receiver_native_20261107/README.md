# Native local gateway receiver evidence

One approved compile and one execution passed on source
`82fa38100ad088c53e564906428789239fe9a285`, 2026-11-07 UTC. This is a
**native receiver/descriptor-owner mechanism PASS**, not full gateway acceptance.

The exact normal CoreC compile command, compiler/linker identity, limits,
process-group handles, stdout/stderr and timestamps are preserved as SDN and
text. All 471 tracked nonvendored runtime C/H input hashes match before/after;
the tracked runtime was clean. The fixture includes the actual socket owner
once and links actual runtime_native.c, runtime_process.c and the normal CoreC
providers. It uses no alternate allocator, registry or fabricated owner success.
The test-owned raw peer sends real SCM_RIGHTS descriptors from real pipes.

Compile exit 0 took 2.1248 seconds; run exit 0 took 0.039386 seconds. Observed
peak aggregate RSS was 130,957,312 bytes during compile and 1,900,544 during
execution. Observed peak allocated artifacts were 1,998,848 bytes, below the
128 MiB cap. CPU affinity was 0–4; compile/run limits 120/15 seconds; aggregate
RSS cap 512 MiB, address-space cap 2 GiB, individual file cap 64 MiB, core dumps
disabled. Resource peaks are sampled observations, not exact instantaneous
maxima. No retry or existing green harness rerun occurred.

The actual assertions cover receive ownership, EAGAIN retention, extra/truncated
descriptor disposal, EOF, shared 16-slot capacity refusal, fixed-binding retry,
one-use adoption, byte/EOF reads, stale generation and wrong binding across a
recycled FD, ordinary-fork refusal, parent byte preservation, and queued-FD close.
They do not fabricate an accepted service connection or group-helper PID.

Binary SHA256:
`a5ffe447a822f5cbd1b9e8827b8aa028c8fd757d68fd1119b7f0831f65f7088b`.
The binary remains in the private build artifact directory; it is not committed.
`manifest.sdn` binds the archived receipts/logs, including the exact supervisor
source. Empty stdout/stderr files are retained where their recorded hashes are
the empty-file hash. The supervisor emitted SDN directly; its Python JSON import
is used only to escape individual quoted strings, not to relabel JSON records.

Distinct-UID listener/sender deployment, real admitted group stdout export,
Simple facade ABI/SSpec, signed application authorization, Host event-loop/control
capacity, durable settlement and Windows transport remain **NOT_RUN/BLOCKED**.
No byte EOF or descriptor close is treated as process termination or released
Host capacity. The separate listener fixture was not executed by this run.

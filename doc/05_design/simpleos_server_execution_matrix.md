# Detail design: SimpleOS server execution matrix

`SimpleOsServerExecutionReceiptV1` contains schema version, mode, source
revision, target identity, OS/kernel identity, executable and image hashes,
filesystem source/path, command, UTC timestamp, exit status, HTTP transcript
hash, DB transcript hash, persistence generation, GPU backend/device/submit/
completion/readback fields, CPU affinity and an error/blocker field.

The ARM fixture builds a current ARM64 image, boots it under QEMU, waits for an
explicit readiness token, resolves the server ELF through VFS, performs HTTP
health/file and DB write/read, shuts down, boots the same image again and reads
the committed value. Every timeout kills QEMU and records failure.

The UNO fixture obtains the physical identity before deployment, writes only a
scoped recoverable directory, hashes the deployed executable, then runs the
same protocol probes. CPU mode rejects a selected GPU backend. GPU mode must
add device, submit, completion and readback evidence while a second HTTP probe
shows that server ownership remained live.

Linux benchmarking pins equivalent processes, warms them equally, and retains
raw samples plus summary. First establish correctness and baseline. If Simple
misses, optimize algorithm, copies/allocations, layout, loop hoisting and
dispatch—in that order—then rerun the same harness. Stop after three cycles.

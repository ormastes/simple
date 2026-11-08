# Captured-process launch admission and thread ownership

Focused Linux native result: PASS, 41 checks, one harness execution. This is a
native C owner regression only, not Simple compiler/SPipe or Windows qualification.

The actual production capture/fork owners were linked into the witness. Cases
exercise ordinary and admitted calls concurrently, deterministic raw-owner
interleaving, wrong-thread/child rejection, expired pre-fork admission, a witnessed
post-fork delay triggering pre-exec expiry, spoofed stderr/nonzero exits, inherited
environment, output limits, timeout cleanup and actual child reaping. The final
clock sample precedes exec/ResumeThread; no atomic user-code-entry timestamp promise
is made across OS scheduling between those instructions.

Capture state now belongs to the calling thread with exact active-child checking,
pthread-key destructor cleanup and prompt output-buffer release after the copied
result. No mutex spans capture wait/drain. Legacy raw setup/wait/getter calls remain
same-thread and must wait before thread exit; destructor closes local descriptors
and releases buffers but does not invent PID-based termination authority.

Resources: taskset CPU 0–4; virtual memory 2 GiB; compile 90 seconds; run 30 seconds.
The first compile did not execute a test: the default mold linker attempted an
8 GiB reservation and failed the cap. Selecting bfd resolved that tool admission
issue. The successful run was not repeated.

[Machine-readable commands and hashes](container_capture_admission_native_20261107/evidence.sdn)
and [captured result](container_capture_admission_native_20261107/result.txt)
retain the exact invocation and outcome. The authored Simple source-contract
spec is NOT_RUN. Windows suspended-child cleanup and full rt mapping/compiler
admission remain NOT_RUN; the Rust ABI twin explicitly refuses before spawning.

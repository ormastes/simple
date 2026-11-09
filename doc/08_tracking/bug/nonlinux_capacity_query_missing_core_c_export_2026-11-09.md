# Non-Linux core-C provider omits the capacity-query unavailable ABI

Status: source repair and focused C/provider checks complete; full tester relink
and execution remain pending independent review and root admission.

The actual c56-produced standalone tester compiled 272 objects but failed its
Windows GNU link on `rt_linux_group_available_capacity_v1`. Its failed linker
response file and all 45 runtime objects were retained; no tester executable or
test assertion run was produced.

`runtime_process_owned.c` includes `runtime_linux_group_owner_impl.h` only for
Linux non-core-only providers. That header owns the real cgroup-backed capacity
measurement. Other providers already have an explicit-unavailable group-stream
adapter, but omitted this capacity query. Its public C prototype was also
Linux-guarded even though the generic Simple test-runner closure references it.

The authored contract returns `[error, available_memory_bytes,
available_disk_bytes]`. `linux_available_capacity_v1` rejects nonzero native
status and nonpositive capacities. The repair exposes the capacity prototype on
all hosts and reuses the existing unavailable-array adapter to return
`[ENOTSUP, 0, 0]` outside Linux or for core-only providers. It does not fabricate
capacity, perform a Linux operation on Windows, replace the Linux implementation,
or introduce a second implementation of the unavailable-array encoder.

The existing non-Unix C selfcheck now verifies the exact three-word error shape
for both an ordinary path and `NULL`/`UINT64_MAX`, and releases both results.
Its small array test provider gains the bounded `rt_array_set` primitive required
by the current process wrappers. The fixture explicitly undefines Linux and
Darwin owner macros alongside the existing Unix/Win32 exclusions; using core-only
instead would hide the value wrappers this fixture intentionally exercises.

Executed evidence is retained under this worktree's
`build/review/linux-capacity/`: baseline `red` compile rejects the absent public
capacity declaration; the first `green` retained an unrelated missing
`rt_array_set` fixture-link failure; corrected `green2` compiles and runs with
exit zero. A revised `green3-linux` compile/run injects `__linux__` and still
returns zero; preprocessing confirms the Linux owner is excluded and the
unavailable body retained. Separately, the actual Windows provider translation
unit compiles as x64 COFF, with exactly one strong capacity-query export.
These checks do not qualify Linux kernel capacity measurement or a full
self-hosted test suite.

The repair base is release `9de91874d5915dff8ed942d27fe501f81a4ba335`.
For the retained 08cee tester objects, a runtime-only continuation must use an
explicit new provider generation carrying only the reviewed minimal ABI delta,
bind every retained object and exact recorded link argument, and leave the
old frozen source, cache and failure receipts unchanged. Wholesale replacement
with newer unrelated runtime sources is not equivalent evidence.

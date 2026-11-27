# Non-Linux core-C provider omits grouped-process unavailable ABI exports

Status: source repair and focused C/provider checks complete; full tester relink
and execution remain pending independent review and root admission.

The actual c56-produced standalone tester compiled 272 objects but failed its
Windows GNU link on `rt_linux_group_available_capacity_v1`. A capacity-only
provider repair resolved that symbol. The next actual linker diagnostic then
reported the complete remaining set: parent acquisition V1 and at-V2, parent
release, broker launch, start, poll, cancel and collect. All eight are repaired
together with capacity as one nine-export provider boundary. Failed response
files and all 45 original runtime objects remain retained; no original object,
frozen source or failure receipt was overwritten.

`runtime_process_owned.c` includes `runtime_linux_group_owner_impl.h` only for
Linux non-core-only providers. That header owns the real cgroup-backed capacity
measurement. Other providers already have an explicit-unavailable group-stream
adapter, but omitted these nine older entry points. Their public C prototypes
were also Linux-guarded or absent even though generic Simple closures reference
them. All nine real Linux definitions already exist in the owned implementation
header at the repair base; these are host-compatibility implementations, not new
runtime primitive names. No fake Simple/Rust counterpart or baseline exception
is warranted to hide a scanner that overlooks owned implementation headers.

The repair exposes the nine prototypes on all hosts and reuses the existing
unavailable-array adapter outside Linux or for core-only providers:

| Operation | Unsupported result |
|---|---|
| Capacity | `[ENOTSUP, 0, 0]` |
| Parent acquisition V1 / at-V2 | `[ENOTSUP, 0, 0, 0]` |
| Broker launch / start | `[0, ENOTSUP]`: zero token, error in slot **1** |
| Poll / collect | Ten words, `ENOTSUP` in slot 0, remaining fields unavailable placeholders |
| Cancel / parent release | Scalar `ENOTSUP`, never cleanup success |

The Simple wrappers reject the nonzero status before using any payload. The
existing encoder deliberately places two-word start errors in slot 1; treating
that result as status-first would falsely create a token. No Linux operation,
state mutation, positive capacity, launch or cleanup success is fabricated. The
real Linux implementation and the existing unavailable-array encoder remain
unchanged.

The existing non-Unix C selfcheck verifies exact shapes and every field across
all nine exports: ordinary paths, `NULL`/`UINT64_MAX`, and tokens 0, 1 and
`INT64_MAX`. All owned result arrays are released. These are sixteen record
results and six scalar results, not a nonzero-anywhere assertion.
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
The expanded `group4-linux` check compiles and runs with exit zero under injected
`__linux__`, covering the complete unsupported family. Its new canonical-profile
Windows object defines exactly nine added strong exports, loses no old global
exports, and covers all 22 Linux-group names referenced by the retained objects.
The genuine compile job completes quiescent under the enforced 2M KiB/300-second
envelope. These checks do not qualify Linux kernel capacity measurement or a
full self-hosted test suite; the complete-family relink remains separately gated.

The repair base is release `9de91874d5915dff8ed942d27fe501f81a4ba335`.
For the retained 08cee tester objects, a runtime-only continuation must use an
explicit new provider generation carrying only the reviewed minimal ABI delta,
bind every retained object and exact recorded link argument, and leave the
old frozen source, cache and failure receipts unchanged. Wholesale replacement
with newer unrelated runtime sources is not equivalent evidence.

# Stage4 omitted the process-timeout owner

## Symptom

The localized runtime-native candidate depends on `rt_process_run_timeout`, but
the already-compiled `runtime_process` object was deleted with the other raw C
objects and never entered strict owner resolution.

## Fix and prevention

Pure-Simple now stages `runtime_process` through the shared deterministic
one-object archive path. Its exact ABI is five process exports on Windows and
those five plus four editor/DAP helpers on POSIX hosts. Actual `rt_*`/`spl_*`
dependencies remain derived from `nm` and must resolve transitively through the
existing candidate owner table; they are not duplicated in a manual list.
The POSIX spawn path now reuses the tagged `rt_array_len`/`rt_array_get`/
`rt_string_data` access already used by both timeout implementations instead of
requesting the duplicate, legacy-layout `spl_*` core API. Its process slice can
therefore resolve through the existing runtime-native, fork, and memtrack
owners without admitting a broad core archive.

Windows capture previously requested the public
`rt_windows_build_command_line` owned by broad `runtime.c`. The quoting
algorithm now lives once in a platform-private static helper: `runtime_process`
calls it directly, while `platform_win.h` retains its public one-line wrapper
for runtime.c-only compiler and standalone lanes. This removes the Stage4
dependency without adding a global export, compile flag, or provider archive.
The Rust core-C/Stage4 cache input list fingerprints the private header while
continuing to derive archive members from `.c` inputs only.

Focused tests pin the hosted archive/object-format matrix, missing/extra ABI
rejection, canonical tagged POSIX argument access, transitive process-slice
selection on POSIX and Windows, shared Windows quoting ownership, process
staging and cleanup, and exact requested-root projection. Broader owner closure
is not claimed complete. Projection and strict final-link routing are
source-implemented, but executable evidence remains pending. No
Simple, C, Rust, Cargo, compiler, or native execution is claimed in this
static-only session.

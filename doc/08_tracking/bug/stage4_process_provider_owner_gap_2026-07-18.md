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

Focused tests pin the hosted archive/object-format matrix, missing/extra ABI
rejection, canonical tagged POSIX argument access, transitive process-slice
selection, process staging and cleanup, and the retained projection barrier.
Broader owner closure is not claimed complete, while Windows still lacks
`rt_windows_build_command_line`. The staged archive is not yet projected or
linked. No Simple, C, Rust, Cargo, compiler, or native execution is claimed in
this static-only session.

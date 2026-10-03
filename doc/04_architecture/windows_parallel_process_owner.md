# Windows parallel owner architecture

The parent runner owns the worker pool, manifest-indexed result slots and process governor. A child receives copied argv/environment and private output/HOME/TMP/cache paths. No child commits parent state. Busy process-slot acquisition returns-3; the parent stops admission and polls existing children before trying the same pending file again.

process_ops routes redirected Windows calls to windows_redirected_process. Its reserved positive tagged tokens are nonreused indices, distinct from legacy HANDLEs. Every recognized tagged token stays in this owner, including unknown/stale values. The facade delegates to the existing windows_process_owner JobObject lease. Collection consumes the lease once only after leader exit AND empty job membership; cancel success requires authoritative terminal collection.

@when target preprocessing keeps Windows FFI imports out of POSIX closure. POSIX retains its existing argv-safe shell redirection. This conditional import path requires native qualification on both platform targets before a cross-platform PASS claim.

Owner tables append lazily and lookup by index in O(1). The100000-start lifetime bound is separate from80 concurrent workers. No100000-slot static allocation is made. Closed slots retain tombstones while clearing handles, pin vectors and facade output-path strings. Historical metadata is O(starts), bounded by two100000-entry registries. Do not claim an exact byte bound from an unverified backend layout. The native1188-start probe records peak RSS and crosses the former1024 limit; full-capacity memory qualification remains a separate measurement.

Expected executable digest is cached per canonical program for a parent lifetime; each admission still hashes/pins actual bytes against it. Replacing a producer at the same path is rejected, not silently re-admitted. Captured files are observed during polling and an overflow cancels/refuses the result; bytes written between observations may exceed the summary cap. This is fail-closed evidence capture, not a disk quota.

Signal/crash containment comes from the retained kill-on-close JobObject. Resource observation failure keeps a lease live for explicit cancellation rather than falsely discarding ownership.
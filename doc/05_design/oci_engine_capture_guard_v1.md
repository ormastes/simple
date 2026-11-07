# Authoritative CLI info capture flags

The existing engine observer used the legacy bounded tuple, which could hide authoritative timeout/output saturation metadata. A syntactically valid info JSON prefix and exit0 could therefore be parsed despite an incomplete captured response.

The observer now calls the existing `process_run_bounded_observed_v1` structured native capture owner and propagates Err. Its live-used processing helper refuses any limit_exceeded flag or nonempty limit_type, nonzero exit status, and oversized stdout/stderr before invoking the unchanged info parser. Ordinary bounded stderr warnings remain compatible. The helper consumes only existing ProcessResult fields: stdout, stderr, exit_code, limit_exceeded and limit_type; it invents no reap or cancellation ownership metadata.

Executable policy/hash/retained-file semantics remain unchanged. Three focused scenarios and their manual are AUTHORED / UNEXECUTED. There was no build, runtime rerun or native qualification; installed probe and Unix fork-origin qualification remain separate pending evidence.

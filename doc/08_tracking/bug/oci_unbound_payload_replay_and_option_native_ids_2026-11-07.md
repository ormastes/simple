# OCI unbound payload replay and option-like native IDs

Status: source repair authored; runtime validation UNEXECUTED.

The release-base provider could return cached create success for a changed
command/arguments under the same pod and attempt. Its V1 journal retained no
payload binding, so a new command-mode flag could not safely establish replay
equivalence. It also accepted `--all` as a native ID through `_safe_token`, which
could become an engine option in cleanup argv.

The binding admission adds immutable payload/operation checks before cache reuse
and effects, strict V2 journal publication, and explicit V1 cleanup migration.
V1 effects require a retained full hexadecimal native ID and exact native label
identity. Every native-ID builder rejects leading `-`. V1 never authorizes new
execution or gains a fabricated V2 digest from cleanup callers.

Prevention source:
`test/01_unit/lib/nogc_async_mut/container/providers/linux/oci_request_binding_spec.spl`.
Negative cases assert actual executor-entry count stays zero for legacy names,
partial IDs, `--all`, malformed requests, and refused publication. Positive
fixtures use exact argv and preserve journal format through cleanup. These are
authored tests; there is no executed PASS or live container qualification.

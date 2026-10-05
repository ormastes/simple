# Environment platform detection calls text methods on an optional receiver

The complete Phase 2 subsystem helper diagnostics include unresolved `lower`
and `contains` calls in `src/lib/nogc_sync_mut/io/env_ops.spl`.
`env_get_opt("OS")` returns `text?`. Testing that value against nil does not
narrow its type under the current language contract.

This is an invalid library use, not an implementation of flow-sensitive
narrowing. See `optional_i64_return_payload_corruption_2026-08-31.md` and
`doc/05_design/language/type_system/flow_sensitive_narrowing_design.md`;
the latter describes a proposed language feature.

The repair binds the payload using supported `if val` syntax in the public
pure predicate `os_value_is_windows`. Explicit visibility permits the native
smoke fixture to call the actual production implementation.
The existing environment facade remains the only OS read. Existing
case-insensitive substring behavior is preserved. The six native smoke checks
in `test/04_smoke/native_env_platform_optional.spl` cover unset, empty, normal,
mixed-case, non-Windows, and substring values without mutating process state.

Validation: whitespace and working/staged environment-facade guards passed.
Independent source review found no P0/P1 issues after explicit predicate
visibility was added. All six native checks
are UNRUN until compiled and executed by a repaired self-hosted producer.
Frozen active bootstrap snapshots are not modified by this repair.

# `mcp_bugdb_spec.spl`: aliased free-function import unresolved (`file_exists as file_exists_backend`)

**Date:** 2026-07-20
**Component:** `src/lib/nogc_async_mut/mcp/bugdb_resource.spl` (and sibling
`resources.spl`, `testdb_resource.spl`, `featuredb_resource.spl` — same
import shape)
**Severity:** High — blocks all 6 examples in the spec file
**Found by:** whole-suite triage campaign,
`test/02_integration/app/mcp_bugdb_spec.spl`

## Symptom

```
error: semantic: function `file_exists_backend` not found
```

on every example (`gets all bugs as JSON`, `gets open bugs only`, `gets
critical bugs`, `gets bug statistics`, `handles missing database
gracefully`, `escapes JSON special characters`).

`file_exists_backend` is not directly referenced by the spec file at all —
it's an aliased import used **internally**, within the same library module
that defines the alias:

```simple
# src/lib/nogc_async_mut/mcp/bugdb_resource.spl:13
use std.nogc_sync_mut.io.file_ops.{file_read_text, file_exists as file_exists_backend}
...
# line 16
    file_exists_backend(path)
```

The spec imports `get_all_bugs, get_open_bugs, get_critical_bugs,
get_bug_stats` from `bugdb_resource`; those functions transitively call
`file_exists_backend`, which fails to resolve even though the alias is
declared and used within its own defining module (not a cross-module
visibility issue).

## Root-cause hypothesis

This resembles the already-documented family in
`generic_class_static_method_unresolved_under_test_2026-07-20.md` (imported
symbols failing to resolve under `bin/simple test` despite being correctly
defined/exported) but with a different mechanism: there it's
`ClassName.static_method(...)` on an imported class; here it's a plain
`use ... {real_name as alias_name}` free-function import alias failing to
resolve for calls made *inside the same file that declares the alias*. Not
confirmed to share a root cause with the static-method family — filed
separately since the failure text and mechanism (aliased-import resolution
vs. static-method dispatch) are distinct, but flagging the resemblance for
whoever investigates either.

## Note

Spec left unmodified — `file_exists_backend` is correctly declared and used
per current import-aliasing syntax; this is an evaluator/resolver defect,
not a stale test.

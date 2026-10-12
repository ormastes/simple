# Native loop callback field type provenance

Status: candidate repair; runtime verification pending.

The admitted Stage 2 compiler matrix's test-runner build reported unresolved
`platform_available_fn` and `execute_fn` calls in
`src/app/io/env_access_host.spl`. Both are function-valued fields of
`HostHardwareProbeAdapter`, called through a `for adapter in probes` binding.

The counted-array loop lowering retained a bare record name but omitted the
declared Array/Slice element HIR type from its new loop local. Entry-closure
lowering can leave the loop symbol untyped, so the existing declared-owner
fallback for callback fields could not recover the binding's type when the
record-name registry missed. The candidate retains that declared element type
on the loop binding without selecting another configured library/provider.

The existing native field-call integration probe now exercises a typed array
parameter, a loop callback, a captured offset, and a returned record. It requires
the callback's actual value 20 and matching label rather than checking only
successful linking. Interpreter and native assertions were authored but have
not run: the general self-hosted test runtime is not yet qualified.

Scoped `git diff --check` passed. This does not establish that the candidate
fully repairs the matrix failure; the rebuilt producer must reproduce and
verify the original entry-closure build before closing this report.

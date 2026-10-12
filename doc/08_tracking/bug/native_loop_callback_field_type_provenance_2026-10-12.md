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

Further matrix evidence includes typed parameter/local callbacks in
`nogc_sync_mut/rt_hal/parallel_executor.spl` and `process_task_arena.spl`.
Their declared-record recovery supplied method identity `module.Name`, which
is nonempty and therefore suppressed the old callback-owner fallback, while
field-layout tables use `module::Name`. The candidate now prefers the declared
registered composite layout even when a method-identity hint is nonempty.
It does not normalize all layout keys or override configured provider families;
the existing construction/read namespace collision remains separately tracked.
A typed-parameter record-returning callback lowering regression is authored,
also NOT_RUN.

The corrected native behavioral probe subsequently reached a distinct closure
conversion error for the capturing, record-returning callback. Its constructor
callee was collected as a free runtime variable; it has a Struct declaration
symbol but no enclosing runtime binding, so closure lifting returned nil.
The candidate excludes exact Struct/Class declarations from free-variable
capture collection and carries field HIR types/ownership metadata into the
fresh lambda lowering. The captured offset remains a real capture. An authored
regression requires one stored and one loaded capture, with no lowering error.
The behavioral probe still requires returned value 20 and label `captured`.
No execution PASS is claimed for this candidate.

The first rebuilt candidate failed closed during bootstrap: the initial loop
patch referred to `iter` inside `lower_for_array_indexed`, where that name is
not in scope. The retained native-build diagnostic names the unresolved global
and rejected the function body; stub fallback remained disabled. Correction
passes the declared element type explicitly from `lower_for_iterator` after its
existing Any/Infer/Error filter. Converted text and dictionary iterables pass
nil and retain their existing behavior. The original callback regressions still
require execution against the corrected rebuilt producer; no PASS is claimed.

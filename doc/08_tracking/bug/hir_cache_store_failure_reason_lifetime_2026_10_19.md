# HIR cache I/O failure reason escapes its scratch lifetime

Status: source repair and regressions authored; runtime verification UNRUN.
Database registration pending: no admitted database CLI is available.

## Evidence and scope

At baseline `4917d9b044f83fbd2a60ffcd78a728f3c05550a5`, the public
`hir_cache_store` wrapper begins a transient scope, calls
`hir_cache_store_in_owned_scope`, and ends the scope on both successful and
failed stores. Its write and rename failure paths call
`_hir_cache_note_store_failure`, which assigned `"io-" + step` to the global
`_hir_cache_last_reason`. The wrapper does not pause or promote that owner.
Later `hir_cache_summary` and `hir_cache_last_refusal_is_io_v1` read the text
after scope reclamation. The existing shard/archive promotion helper does not
cover this public-wrapper path.

This is a source-established dangling diagnostic root, with real I/O failure
triggers already represented by the store-failure spec. No new runtime crash
was executed. It is not an attribution of the historical 19 HIR-worker
SIGSEGV outcomes, the scalar-three codec loss, or the 83 GiB MIR retention
failure. Those investigations retain their prior status. Host swap occupancy
does not establish any of these source defects.

## Repair and lifetime argument

Both private failure call sites now pass the complete literal `io-write` or
`io-rename` separately from the existing human-readable step. The helper
assigns that reason directly; it does not allocate a concatenated string.
Counters, first-failure logging, temporary-file cleanup, return values and
cache-admission checks keep their existing behavior.

The lifetime claim uses the actual native owners: LLVM
`_MirToLlvm/core_codegen.spl` and `cranelift_codegen_adapter.spl` lower literal
strings through `rt_string_new_literal`; `runtime_native.c` implements that
entrypoint using `rt_string_new_uncached_persistent` and shared literal
interning. Ordinary concatenation does not have that persistent lifetime.
The two helper call sites must continue passing literals. The existing
`hir_cache_promote_diagnostic_owner_v1` API remains available to archive/shard
callers. No new graph retention, allocator change or guard bypass is needed.

## Regression and qualification

`test/01_unit/compiler/driver/hir_cache_store_failure_reported_spec.spl`
forces a write failure using a regular file as a cache-directory ancestor and
a rename failure using a nonempty directory at the final cache-file path.
Both scenarios check failure counts, absence of a published store and temporary
file, the exact retained reason and I/O classification after a new real scratch
allocation/reclamation cycle. The rename case also requires the blocking
directory's marker to survive. Assertions execute outside the scratch scope.
No synthetic failure switch or successful placeholder is introduced.

Static checks only: diff whitespace, the two literal call sites, absence of
dynamic reason construction, and executable-spec layout. Native execution,
the before-fix negative control, branch coverage, full compiler/lib checks,
MCP/LSP smokes and SPipe generation remain UNRUN. A passing interpreter spec
would not qualify native reclamation. The native before/after probe must use an
admitted self-hosted producer, private output/cache and existing resource
limits. Run diagnostics with optional memory instrumentation off as requested;
failure to reproduce the old dangling read must be reported, not relabeled a
successful negative control.

This work is based on the primary development lane. Frozen producer source
`43925ae2cc8a05e397cab12122aec823b22f3005` and its prepared execution packet
were not edited and do not contain this repair. No current or future run of
that frozen producer establishes execution coverage for this patch. Root owns
independent review, integration and any separately admitted compiler execution.

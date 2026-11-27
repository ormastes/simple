# Declaration metadata pools survive the per-file AST reset

Status: source fix and production SPipe regression supplied to the integrated
producer rebuild; runtime qualification pending. Apply together with the
coordinated `spl-flatpool-v2` codec change. Do not deploy this serialization
change with the old codec version.

Five arrays appended by every declaration allocation were absent from
`ast_reset`: `decl_asm_placement`, `decl_unroll_factor`, `decl_pipeline_ii`,
`decl_memory_banks`, and `decl_param_default_text`. The scope investigation
observed a saved frontend cache frame with declaration count 14 but 27,411
entries in both the banks and defaults arrays. The append/reset source audit
confirms the retained tail: 42 parallel declaration pools were appended, but
only 37 were cleared. This is distinct from intentional retained HIR modules
and symbol snapshots, and does not establish attribution for every OOM event.

The owner-local `decl_metadata_pools_reset` initializes and clears all five
arrays; `ast_reset` invokes it. Four already serialized pools now restore in
place so their persistent owners do not become dangling transient arrays.
Assembly placement, previously absent from the cache payload, is serialized
and restored in place too. The coordinated format version invalidates old
entries normally; existing cache files are preserved.

`flat_decl_pools_consistent` validates scalar declaration/module counts,
all 42 declaration array lengths, and the active module declaration indices.
It permits a preallocated unused module slot tail: existing `module_add_decl`
can write into such slots before growing the owner. The strict codec workstream
calls this helper before accepting a restored frame.

The production regression `decl_metadata_lifetime_spec.spl` exercises repeated
large/small resets, a real dump/restore with exact banks/default-expression-ID/
assembly/unroll/pipeline values, failed truncated restore followed by reset and
fresh declaration values, and malformed lengths/active indices with a valid
preallocated-tail control. The separate strict frontend integration regression
covers actual corrupt-cache-to-parser fallback. These tests are unexecuted on
the refreshed producer at this handoff; cross-module mutation in the negative
fixture must be diagnosed if it fails, never replaced by a vacuous assertion.

Bounded old-producer qualification stopped after three attempts. Two native
projections of the actual pool methods failed because producer 908 could not
lower array `.clear()` in the reduced closure (ordinary and bootstrap modes).
An explicit runtime-clear ABI adapter then exposed missing-return diagnostics
for inferred non-unit functions. No fallback stubs were permitted, no native
pool memory result is claimed, and production methods were not rewritten to
accommodate the probe. Logs and source projection are retained under
`/mnt/simple-bootstrap-6b2/cli-memory-route-fix-20260930/pool-regression`.

The codec completeness check initially reported two existing payloads as
missing because their encoding uses reconstructed local arrays: `arm_body`
and `decl_body_stmts`. The separate checker fix traces the complete same-function
sequence from the authoritative text mirror through the local reconstruction
to the encoder call, without exempting any pool names. Its arbitrary-name
positive fixture and missing-copy, wrong-temporary, wrong-item, and
cross-function negative controls all passed in the checker's built-in selftest.
The complete scan then passed all 171 pools; evidence is
`pool-regression/codec-completeness-fixed.log`. This structural PASS does not
qualify the pending production runtime regressions above.

## Diagnosis append 2026-11-05 (release/1.0.0 re-run, agent00 timeout batch)

The fourth example ("rejects mismatched metadata lengths and invalid active
module references") still fails under `bin/simple test` with
`expected true to equal false`. Diagnosed root cause: the example's negative
controls inject corruption by pushing directly into the module-level arrays
imported into the spec (`decl_memory_banks.push(123)`,
`module_decl_slots[0] = 1`). Under the test runner's JIT co-compilation, those
imported bindings do NOT alias the module instances that
`flat_decl_pools_consistent` reads (duplicate co-compiled module state — the
same interpreter struct-mutation-visibility family noted in
convert_nodes_loud_fallback_spec.spl's HARNESS NOTE). Instrumented re-run:
after `decl_memory_banks.push(123)` the spec sees `banks_len=2` while
`flat_decl_pools_consistent()` still returns `true` (it reads the un-pushed
owner instance). The identical sequence run standalone via
`bin/simple run` (probe build/scratch/probe_meta2.spl) returns the correct
false/true/true/false for all four controls, so `flat_decl_pools_consistent`
itself and the retention fix are correct; only the cross-module mutation
injection is invisible under the test harness. Not fixed here: per this
doc's own instruction the negative fixture must not be replaced by a vacuous
assertion; a real fix needs either loader/JIT module-instance dedup
(99.loader lane) or an owner-module corruption-injection hook called instead
of direct array mutation.

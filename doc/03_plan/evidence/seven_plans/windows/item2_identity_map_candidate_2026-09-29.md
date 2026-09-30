# Item 2: pure identity-map candidate transitions

Scope: the in-memory allocation portion of selected REQ-004. This is partial
implementation, not completion of the distributed textual database plan.

## Acceptance and ownership

- AC-1: retries preserve the permanent alias and do not consume numbers.
- AC-2: tombstones preserve reverse resolution and prohibit number recycling.
- AC-3: namespace rejection preserves the supplied state; kinds allocate independently.
- AC-4: retained high-water controls allocation even without live rows; u64 exhaustion rejects.
- AC-5: a high-water regression is rejected before new allocation or retry resolution.
- AC-6: document the candidate-state boundary and remaining integration work.
- AC-7: duplicate forward/reverse bindings and relabeled namespaces fail closed.

Owner: `src/lib/scv/distributed_identity_map.spl`. Existing identity validation
and canonical encoding are reused from `distributed_identity.spl`; no duplicate
identity wire encoding, runtime extern, C, C++, or Rust logic was introduced.
The module returns a new candidate value. The settlement owner must persist
that complete value with accepted-batch and receipt state under its existing
writer lease. The module does not authorize allocation or attest durability.
Loaded state must still pass settlement admission; this is not a deserializer,
signature validator, or authority check. Public operations validate internal
binding and allocator consistency. Bindings retain typed UID provenance and
must match their canonical identity, namespace, and kind. Duplicate identities,
duplicate kind/sequence aliases, and duplicate high-water kinds reject.
This bounded candidate implementation uses quadratic duplicate validation;
large-database indexing and NFR qualification remain outstanding.

## Test-first diagnostic evidence

Spec: `test/01_unit/lib/scv/distributed_identity_map_spec.spl`.
Manual: `doc/06_spec/01_unit/lib/scv/distributed_identity_map_spec.md`.

Runner: `C:/Users/User/dev/simple-bootstrap-main-windows/.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-gnu/stage2-runtime-authority/simple.exe`.
SHA-256 previously recorded for this Phase-1 seed:
`6456107ce86e91d06a03171873b141632b819b8a59637f9fab414e0dcee0dae6`.
Invocation: `test test/01_unit/lib/scv/distributed_identity_map_spec.spl --mode=interpreter`,
with `SIMPLE_LIB` set to the isolated publication checkout's `src` directory.

Initial test-first run exited 1 before the owner existed; its noisy diagnostic
tail did not retain the exact cause, so that exit alone is not claimed as an
assertion failure. The initial implementation then reported 3 executed passes.
An additional regression test captured a precise failure before its fix:
`expected existing to equal SCVDB_ALLOCATOR_REGRESSION`, with 4 passes and
1 failure. Allocation now checks high-water against retained bindings before
resolving retries. The resulting run exited 0 with `executed=5 passed=5 failed=0`.

Review found duplicate binding and namespace relabeling gaps. The final bounded
cycle first added regressions: 7 examples, 5 passes, 2 failures, including
`expected existing to equal SCVDB_BINDING_AMBIGUOUS` and an incorrect reverse
identity returned under a foreign namespace. Shared invariant validation now
runs before allocation, tombstoning, and reverse lookup. The final diagnostic
run exited 0 with `executed=7 passed=7 failed=0`.

Local diagnostic logs:
`build/native_probe/item2-identity-map/red-regression.log` and
`build/native_probe/item2-identity-map/cycle2.log`, followed by
`build/native_probe/item2-identity-map/red-binding.log` and
`build/native_probe/item2-identity-map/cycle3.log`.
Green suites were rerun only after changed scenarios or implementation. Three
implementation/fix cycles were used; no further cycle is authorized in this
scope. No native compiler or linker was invoked by this interpreter check.

## Unfinished gates

This is authorized Phase-1 diagnostic evidence, not self-hosted SPipe admission
or Windows/Linux completion. Native execution, required compiler/lib/MCP/LSP
checks, admitted docgen/sspec-maintain, coverage, and performance qualification remain
open. Five broad system checkers in the existing distributed-database system
spec remain fail-fast; none was replaced by a placeholder success.

REQ-004 still requires atomic durable forward/reverse storage, accepted batches,
merge/split links, and settlement integration. The overall plan also requires
authority fencing, signed receipt rollback detection, transport CAS/read-back,
CI/provider ingestion, retention, and two-clone recovery. This candidate helper
does not satisfy those requirements. Guides and shared process skills are
unchanged because no user-facing command or workflow was added.

## Diagnostic manual generation (2026-09-30)

The previously recorded Phase 1 runner generated the mirrored manual from
the final seven-case executable spec using `spipe-docgen` with `--no-index`.
It exited 0 and reported one complete document and zero stubs. The generated
steps and concrete identity/high-water assertions were inspected. This replaces
the earlier short hand-authored companion, but does not claim admitted SPipe
execution or maintenance scores. No unchanged passing test was rerun.
Log: `build/native_probe/item2-identity-map/docgen.log`.

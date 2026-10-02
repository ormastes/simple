# Ordinary parsing retains unscoped scratch

Status: concrete source defect and guarded resource failure; regression prepared,
native counterfactual UNRUN, production repair NOT IMPLEMENTED or accepted.

## Bound evidence

Producer SHA256: `e7ec89c1f106353cc8fdc792d5d41359336c72287f410aa039b57d8f6101dfdf`,
built from selective source `6b9edd328cc2fd3d7372c2c685a1b2256999fa1c`.
Diagnostic input source: `ba066da503e50a386294e27f9e09ecbd27373add` at
`D:/dev/windows-provisional-memory-source-20261002`. The relevant frontend,
module assembly and driver parsing files are identical between those commits.

Under `D:/dev/bootstrap-memory-fix-validation-20261002/phase34-direct-v3/`:

- `phase4/llvm/binaries/full-cli/compile.stdout.log`: parse stopped at 646/2491,
  before `src/app/devhub/backend_resolve.spl` completed. Its process-tree receipt
  recorded a 6,837,064 KiB peak and a 7 GB guard stop.
- `phase4/llvm/binaries/test-runner/compile.stdout.log`: HIR stopped at 24/610,
  before `lib.nogc_async_mut.test_runner.doc_generator` completed; peak
  6,838,156 KiB. This does not isolate its HIR growth from the retained parser
  baseline and is not evidence that one parser repair fixes all HIR growth.
- `worker.shs` clears bootstrap/stage4 flags, enables frontend caching, and
  invokes ordinary native-build. No streaming scope is requested there.

No unchanged failed build was retried for this investigation. The external
7 GB process-tree cap remains unchanged. The successful hello with the internal
diagnostic sink disabled is not full-module memory acceptance.

## Concrete ownership gap

`driver_source_pipeline_parsing.spl::parse_full_frontend_selected_v1` calls the
ordinary frontend with borrowed scope false. `frontend.spl` supplies streaming
scope false as well. `_FlatAstBridge/module_assembly.spl` starts a scope only
when streaming scope is true. Consequently ordinary parsing retains temporary
lexer objects, flat AST pools, bridge intermediates and preprocessing/hash
allocations for process lifetime even after a returned ParserModule owns the
needed graph. Cache hits rebuild through `build_module_from_flat_pool_blob`,
which also has no local scope. The separate cold cache serialization scope
does not cover these earlier/later allocations.

Retaining all requested executable ParserModules is intentional. Retaining
discarded scratch from every file is not necessary for that behavior. The
proposed repair is a driver-owned per-file scope around the existing borrowed
frontend route, promoting the complete result and escaped owners before the
existing ordered cleanup. It must cover cold and warm parsing without changing
inventory, cache identity, target decisions, diagnostics or public metadata.

## Escaped-owner audit: not yet complete

| Owner | Required disposition |
| --- | --- |
| Result ParserModule or error | Promote complete reachable graph, including spans/text/body metadata |
| Target cfg receipt | Preserve current source decision and containing map growth |
| Aspect/effect/criticality/layer registries | Existing promotion helpers; confirm all pending metadata |
| Private frontend cache scope memo | First nonempty environment result must outlive a parser scope |
| Shared parse authority path/digest/rows | Preserve first load and changed-identity publication; avoid repeatedly walking unchanged full inventory |
| Resource registry names/index/metadata | Reset on each parser init, but last-module public query lifetime must remain valid |
| Unsafe/enum annotation globals | Audit consumers after parse versus next-file reset before reclaiming |
| Advisory correlation slot | Scalar-only, initialized outside parsing; no discovered scoped text payload |
| Lexer/interner/AST globals | End arena before replacement, using existing cleanup order |

Merely reusing the existing four-registry helper is insufficient to establish
safety for a new blanket ordinary-parser scope. No production edit is made
until this audit and native regressions establish valid escaped ownership.

## Native counterfactual

`test/fixtures/ordinary_parser_retention/main.spl` retains all 128 function
bodies per module. Ordinary and scoped-reference modes run in fresh processes,
report bytes/objects after each file, and validate every earlier and last
module after later arenas close. Cold and warm modes assert actual parser work
and cache hits. The reference primes the immutable private cache memo outside
its scope, disables shared CAS, and uses plain functions; it is intentionally
not a safe general production wrapper and cannot qualify annotation/registry
ownership. Its role is to separate intended retained AST from transient scratch.

Native execution, performance comparison, annotation-owner coverage, full
module completion and peak-RSS acceptance remain pending. Do not mark this
issue fixed based on the source diagnosis or fixture alone.

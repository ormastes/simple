# Ordinary parsing retains unscoped scratch

Status: partial production candidate implemented for ordinary AOT parsing;
native counterfactual UNRUN and candidate NOT ACCEPTED or deployed. Coverage,
MC/DC, full-inventory target-cfg selection and non-AOT retain the prior route.

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
candidate uses a driver-owned per-file scope around the existing borrowed
frontend route, promoting the complete result and escaped owners before the
existing ordered cleanup. It must cover cold and warm parsing without changing
inventory, cache identity, target decisions, diagnostics or public metadata.

## Candidate ownership and explicit exclusions

| Owner | Required disposition |
| --- | --- |
| Result ParserModule or error | Promote complete reachable graph, including spans/text/body metadata |
| Target cfg receipt | Excluded from the new scope: containing Dict/CompileContext mutation lifetime is unproven; needs preparation then publication after scope end |
| Aspect/effect/criticality/layer registries | Existing promotion helpers; confirm all pending metadata |
| Private frontend cache scope memo | First nonempty environment result must outlive a parser scope |
| Shared parse authority path/digest/rows | Preserve first load and changed-identity publication; avoid repeatedly walking unchanged full inventory |
| Resource registry names/index/metadata | Reset on each parser init, but last-module public query lifetime must remain valid |
| Unsafe/enum annotation globals | Promote last-module metadata; rich declarations retain their own complete graphs |
| Parser token slots and diagnostics | Promote seven owners; native first-file allocation must survive reuse by the next parser initialization |
| Advisory correlation slot | Scalar-only, initialized outside parsing; no discovered scoped text payload |
| Lexer/interner/AST globals | End arena before replacement, using existing cleanup order |

The candidate preserves these roots through a shared owner helper used by
production and the reference fixture. A scalar parser initialization generation
distinguishes errors returned before parsing: those preserve their Result but
do not try to promote uninitialized native parser/registry globals. A prior
draft incorrectly promoted target-cfg state only on success; excluding that
route preserves its existing mutation/error behavior until its containers have
a proven lifetime. Coverage/MC/DC inventory requires a separate owner contract.

Private/shared cache memo helpers promote only newly published owners. They
do not repeatedly walk an unchanged complete source-authority dictionary.
Registry promotion still traverses retained semantic claims; native timing on
representative input is required before claiming no performance regression.

## Native counterfactual

`test/fixtures/ordinary_parser_retention/main.spl` retains all 128 function
bodies per module. Ordinary and scoped-reference modes run in fresh processes,
report bytes/objects after each file, and validate every earlier and last
module after later arenas close. Cold and warm modes assert actual parser work
and cache hits. Only the reference primes its private cache memo; ordinary AOT
starts cold to exercise first allocation. Both retain complete bodies and
share the escaped-owner promotion helper. Timing uses plain functions and
private caching to separate retained AST from transient scratch.

Outside the timed region, native cases validate resource/unsafe/enum metadata,
diagnostics across error recovery, early advisory rejection before parser
initialization, and shared-authority first publication/reuse/digest rejection/
restoration across actual scopes. Shared checks use a real cached flat-pool
payload and the immutable publisher/read APIs. Complete is emitted only after
all semantic cases pass; native execution of these cases is still pending.

Native execution, performance comparison, full-inventory/coverage ownership, full
module completion and peak-RSS acceptance remain pending. Do not mark this
issue fixed based on the source diagnosis or fixture alone.

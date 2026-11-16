# Original declaration binding for visibility source facts

This source checkpoint stacks the named-aspect owner change
`e51a1f0c64146c5585313e2c274626b2a58e7d35` and declaration observations
`b32d16f352c6b8f28b0d47a3959a73cdea773529`. It implements the next binding
step requested for the full visibility work. It does not change legacy
`Visibility`, member privacy, resolved exports or requester permissions.

## Binding contract

The module dispatcher captures an observation row index before parsing the
declaration. After a parser returns its original declaration, the dispatcher
registers that node and binds the explicit row to its raw declaration ID.
The generic `module_add_decl` remains unchanged. Enum and class parsers can
register synthetic implementations before returning their original node;
those implementations and their methods acquire no top-level intent binding.
The generated newtype implementation likewise stays unbound.

Rows start with declaration ID `-1`. Missing, generated, unsupported and
registry-only declarations remain unknown, never implicitly omitted.
In particular, a named aspect currently has only a lexical container name:
its advice nodes are emitted by the helper, and this change does not invent a
container declaration ID. Macro and unit helpers without returned original
nodes remain unbound. Specialized decorator arms that consume a declaration
without returning through the observed module dispatch remain unbound too.
This table is therefore a partial, explicit binding table, not an exhaustive
scope classifier.

An admitted table has aligned arrays, increasing byte offsets, known modifier
codes and unique bound IDs. Every bound ID must be in the raw declaration pool
and in the top-level module declaration set. Registration is constant work
per declaration; uniqueness/membership validation builds maps once per
validation rather than rescanning all earlier bindings on every insertion.

## Snapshot and cache identity

`parser_init_with_path` clears prior observations and records the source path
and SHA256 of the selected preprocessed lexer input. Prefix offsets refer to
that selected input. Preprocessing can blank directive lines, so these are
not claimed to be raw-file byte offsets. A future raw-source consumer needs
the preprocessor's source mapping, not an assumed identical offset.

The combined cache header is
`spl-flatpool-v18-aspect-owner-declaration-intent-binding-v1`.
Neither the standalone visibility-v17 header nor the standalone
`spl-flatpool-v16-field-array-sizes-aspect-owner-v1` header is accepted.
The combined pending payload adds declaration IDs, selected-source digest
and path in fixed sorted order. Legacy private entries are never reinterpreted.

Binding admission is transient and is not serialized. Restoring pending
metadata alone cannot authorize its raw IDs against an unrelated AST with
recycled indices. Whole-frame restore admits only after every family, final
canonical frame and declaration consistency check succeeds. Any late failure
clears the facts. A whole ParseContext move similarly admits after all owners
are installed; a pending-state move alone does not. Cache-to-module conversion
also compares the restored path and selected-source digest with the requested
input before constructing the module.

## Bridge and consumer boundary

`ParserDeclarationIntentV1` retains the raw ID, selected-source prefix offset,
modifier, declaration kind and name. `ParserModule` owns these rows plus the
selected-source digest; its `name` supplies the source path. The flat bridge,
async module reconstruction and `ModuleSurfaceParserOwner` round trip retain
the metadata. Raw IDs are meaningful only inside this snapshot, never durable
cross-module symbol identities. No permission can be inferred from name alone.

HIR surface identity and semantic cache digests do not yet consume these facts.
That next step must bind source facts to resolved declarations and incorporate
them into semantic cache identity before implementing omitted folder-local,
explicit-pri file-private, ordinary-pub feature-public, binding-aware layer
exports and requester access. The live LSP source-reader draft remains a
separate transport lane; it does not acquire those semantics from this patch.

## Verification and limits

The executable binding spec exercises real enum parsing with a synthetic impl,
same-shaped interleaved parses with recycled IDs, full cache restoration,
duplicate/non-module/out-of-range ID rejection, late-frame failure, predecessor
header rejection, bridge/source identity, ParseContext moves, module-owner and
async rebuilds, and preservation of lexical named-aspect ownership.
It also checks selected-source identity after preprocessing, initialization
without a parse, and the explicit unknown status of directly consumed decorators.

These new tests have not run. Native qualification remains **UNQUALIFIED**.
The exhausted parser and LSP native attempts recorded in the earlier design
reports are preserved; this branch does not reset that history or retry them.
Full compiler/lib/MCP checks, runtime smoke, native execution, coverage and
performance measurements remain pending. The additional selected-source hash
and validation maps require measurement with an admitted producer.

Static checks: working-tree direct-env guard passed; executable spec count
under `doc/06_spec` is zero. The flat-pool audit checks 166 pools and still
reports the two documented baseline omissions, `named_type_modules` and
`par_error_records`; no new payload omission was reported. This is a source
checkpoint for review, not merge or full-visibility acceptance.

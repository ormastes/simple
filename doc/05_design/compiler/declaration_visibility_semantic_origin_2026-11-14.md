# Declaration intent through typed AST and HIR

Status: semantic-origin groundwork source-reviewed; requester integration in progress; runtime unqualified.
Base: `239ca96084d`, the combined original-source binding checkpoint rebased
without patch changes onto release `73a1585dc654`.

The selected policy remains: an omitted top-level modifier is immediate-folder
scope; explicit `pri` is file scope; every ordinary `pub` is classified
featurePublic, subject to legal module/export routes and closed ancestors.
featurePublic is not an arch feature-package access modifier. Verified absence
of ancestor manifests preserves open-module public handling; incomplete
readsets remain unavailable. Layer promotion belongs to a resolved export binding,
never to the original declaration. Scoped and member rules remain separate.
Legacy Private records cannot be reinterpreted as omitted source syntax.

## Directory interfaces and source migration

A present `__init__.spl` is a closed directory interface, including an empty or
comments-only file. It exports nothing unless an explicit legal route opens it.
A `pub mod child` route and a selected named-export binding are alternatives:
the selected binding can expose a legal declaration without publishing its
implementation module. Neither route can promote explicit `pri`.
Authenticated complete absence of a manifest retains the existing open public
module route. Missing or incomplete evidence cannot be treated as absence.

This changes source-facing access in trees with existing empty initializer
files. For example, `src/compiler/__init__.spl` describes auto-discovery in a
comment; discovery establishes lookup, not permission. Cross-boundary clients
will need explicit public child routes or selected facade exports. The compiler
must diagnose that migration rather than grant access from the old comment.
Source routing selectors do not truncate the ancestor chain; observation
continues to the authenticated inventory family boundary.

## Exact source origin

The flat bridge records raw declaration IDs at actual typed dictionary writes.
A later write replaces that target's ID, including a synthetic write using -1.
An observation receives a category-qualified `projection_key` only when its
original raw ID still owns that exact target. Multiple surviving targets for
one raw ID are rejected. Unprojected source observations remain useful source
facts but confer no typed declaration policy. Duplicate target/ID facts are
rejected by the typed index builder; malformed input makes semantic projection
uncacheable rather than choosing a dictionary iteration winner.

Source-owner admission requires canonical ParserModule.name to match the
consumer source path and a nonempty selected-source digest. Surface
declaration-authority rows retain modifier, canonical source path and
typed target key alongside the existing logical terminal owner. Export-origin
resolution copies these immutable terminal facts to the alias row without
changing the modifier. Declaration semantic identity includes sorted typed
keys and modifiers; frozen identity additionally includes binding, terminal
owner, source name, target and path. Parse-local IDs, offsets and selected-source
body hashes are excluded, preserving body-only dependency cache hits.

HIR carries four defaulted text fields on HirSymbol: declaration_modifier_v1,
declaration_source_path_v1, declaration_projection_key_v1 and declaration_owner_v1.
Empty means Unknown. Local lowering attaches facts to the symbol returned by
the actual typed declaration conversion. Imported attachment validates symbol
kind, spelling and terminal owner. Transparent type aliases sharing a target ID
do not replace that target's origin. Rebinding conflicting known origin fails.
Rename, nominal relocation and verification snapshots preserve these fields.
Standalone lowering without a canonical module filename remains Unknown.
The authority digest uses the established repo-relative cache path identity,
while runtime source identity retains its canonical physical path. A snapshot
root move must not invalidate a body-only cache hit or rewrite a declaration
path into the importer path. The existing authenticated snapshot-root cache
rebind rewrites the new path scalar alongside spans; its production cache
regression now checks the origin path and preserves logical owner/modifier.

## Required access integration

This slice is not folder-scope enforcement. Actual parsed manifest metadata,
authenticated positive/negative ancestor reads and a frozen permission graph
are being implemented in the separate manifest producer lane. Their common
DTO contract is ParserManifestVisibilityV1 plus VisibilityManifestReadV1 and
SourceFile reads/root/snapshot/complete fields. Missing authority is unavailable,
never inferred from query substring matching, directory names or is_public.

Canonical SymbolIds can be shared by aliases. A requester permission bit on
HirSymbol would let an authorized facade authorize the direct implementation
path. Keep the resolved binding handle and its permission separate; check the
actual selected binding before lowering. Internal dependency materialization
must not impersonate an explicit requester import. The source authority index now retains category-qualified bindings, including
same-spelled types and functions; typed lookups refuse mismatched categories.
Transparent aliases still require their own selected binding policy in the
requester consumer. The current semantic checker still admits is_public globally.
The exported mutable-static helper still mixes linkage and declaration
visibility; full integration must separate them and never promote explicit pri.

## Codec generation and qualification

HIR schema v20/canonical v10 rejects v19 records lacking source intent.
Generated codec bytes came from the admitted native codec generator SHA256
`2b78217c925aa434aa1c5c4c0846ecdffccbbbac05f395f500ee24073749319c`.
Its generator source directory is unchanged from ecb2d505 to release73a1585.
With the current nine unmodified schema inputs, real generation produced 99
declarations and matched the checked-in codec byte for byte (2.118 seconds,
565,477,376 bytes peak tree RSS). With the four appended fields, generation
produced 99 declarations (1.928 seconds, 560,422,912 bytes peak tree RSS), SHA256
`90cb3c46e80d5e060734fb22d97d2067690a36ec014b6e58d77cba48d42f0ee9`.
Both runs used actual descendant RSS monitoring, 1 GiB/30-second caps, no AS
limit, and restored all borrowed generator inputs/output afterward. Source
snapshots and receipts remain in `build/visibility-codec-generation/`.
This proves actual regeneration only, not compilation or execution of the new
schema or visibility behavior. No exhausted parser/LSP native lane was rerun.

Authored regressions cover duplicate typed targets, enum synthetic nodes,
omitted-vs-pri semantic identity, origin overwrite/alias protection, and real
frontend/HIR/cache roundtrip with old-header rejection. They remain unexecuted.

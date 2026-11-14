# Selected-binding requester decisions

Status: implementation in progress. This document does not claim enforcement
or runtime qualification. The semantic-origin checkpoint is source-reviewed;
its fields alone do not authorize a request.

## Inputs and ownership

The frozen module-surface registry owns declaration authority, selected import
and export routes, physical source identity, and generation. The manifest
producer owns complete inventory ancestry, positive/negative reads, selected
frontend facts and configured child-module resolution. HirLowering owns the
source expression's actual lexical or qualified binding selection.

The decision joins all three owners. It never derives access from a canonical
SymbolId alone, from a path spelling convention, or from `is_public`. A direct
qualified implementation lookup and a facade alias can share a symbol while
requiring different decisions. A policy decision is not a new declaration
modifier and cannot mutate terminal declaration intent.

`lookup_binding_scope_raw_v1` shares the existing native-safe scalar scope walk.
`lookup_binding_v1` returns the actual found scope, requested spelling and live
symbol ID. Existing lookup wrappers use the same walk without allocating a
binding receipt. This selected tuple is request-local; it is not permission and
must not survive symbol-table reset or mutation as a permit.

A source alias's route association must be attached at the actual binding write.
Its identity includes scope, spelling, selected symbol, registry generation and
binding mutation version. Same-ID rebinds need distinct versions; testing only
symbol ID is insufficient. Per-spelling versions must retain tombstones across
unbind/rebind. Scope now carries those versions at the four actual mutation
owners; all independent scope-copy owners clone the version dictionary. Same-ID
rebinds advance it, no-op bind-if-free and unrelated spellings do not. The actual union codec now preserves these versions under the distinct
v21/canonical v11 schema. Requester route-map lifecycle integration is still
pending; reset versions alone cannot invalidate a retained permission map.
Internal
materialization flags are not evidence of a user import: both explicit imports
and dependency loading set `registering_import_symbols`.

## Decision order

1. Validate requester, selected binding surface and typed declaration handle
   against the same frozen registry generation. Require the bound selected-source
   owner admission already implemented by the origin checkpoint.
2. Explicit `pri` permits only the same physical file and cannot be promoted.
   Omitted syntax permits immediate-folder use. Unknown legacy Private remains
   Unknown; it cannot be reclassified as omitted.
3. Ordinary `pub` is featurePublic regardless of arch dimension. It still needs
   a legal selected module/export route. Scoped modifiers use their existing
   peer, parent, package and friend rules; member rules remain separate.
4. Validate every crossed directory observation through the canonical inventory
   family boundary. Complete authenticated absence is open. A present manifest,
   even empty, is a closed interface. Missing/incomplete evidence is unavailable.
5. A resolved public child route can open the selected module route. A selected
   named-export binding is an alternative, with its own resolved hop provenance;
   it does not require publishing the implementation module. Validate eligibility
   at each export hop, and reject cycles/ambiguity/missing origin. A facade grant
   never authorizes a later direct implementation lookup.
6. Apply containing-type and member checks to the actual member selected. A
   public member cannot bypass a rejected containing type.

A child target is authoritative only if the existing configured resolver used
frozen observations for candidate existence and directory enumeration. Checking
that a live-selected winner happens to be in the snapshot is insufficient.
Positive policy facts also depend on selected frontend/configuration identity,
not only the raw manifest SHA. Policy-only manifests stay outside ordinary
compile/import traversal unless an actual import selects them.

## Source-use integration inventory

The requester decision must run after actual selection on all these routes:

- Explicit, namespace, glob and lexical import bindings in
  `_Items/module_import_resolution.spl`; lexical statements retain their scope.
- Identifiers and module-qualified calls/fields in `expression_core.spl`, plus
  struct/enum construction. Preloaded symbols do not bypass the decision.
- Bootstrap/global fallback in `expression_support.lower_unresolved_ident`.
- Bare and exact-qualified nominal type hits in `types.lower_named_kind`, and
  the existing-symbol fast return in `resolve_qualified_named_type`.
- Transparent alias selection before `lower_named_symbol_kind` switches to the
  declaration owner's scope. Expansion of an already authorized alias's target
  and default types is internal declaration work, not a second user binding.

The current post-HIR visibility checker admits public symbols globally. It
cannot remain the authority for known source facts after this integration.
Exported mutable static linkage likewise needs separation from declaration
visibility; its current unconditional Public promotion cannot promote `pri`.

## Cache and request behavior

No filesystem scan or subprocess belongs in a source-use decision. The frozen
registry retains policy records and exact route handles. Semantic cache identity
must include policy schema, typed source intent, terminal logical owner,
snapshot-relative source identity, resolved binding hops, selected policy facts
and authenticated positive/negative manifest observations. Body-only edits that
do not alter these facts retain their existing semantic-cache behavior.

Binding revisions prevent stale route association within a lowering owner.
Registry generations prevent association across source snapshots. Cache-hit HIR
must be admitted by the same policy identity; adding a missing initializer must
invalidate a previous open-directory decision. A source-only checked result is
not evidence for old HIR artifacts that lack these facts.

## Required regressions

Author executable cases for same-file pri, sibling-file pri denial, same-folder
omitted success, nested-folder omitted denial, ordinary pub without arch facts,
complete absent manifests, empty closed manifests, public child routes, selected
exports without public implementation modules, explicit pri export rejection,
closed intermediate ancestors, alias-to-direct-path rejection, same-ID rebinding,
shadowing, containing-type privacy, all existing scoped/member rules, positive
manifest mutation and negative-to-present cache invalidation. Exercise both
registration and already-present symbol/type shortcuts. Existing native attempt
caps remain exhausted; no tests in this packet are reported as executed.

## Known private-target rejections

Declaration origins are now attached to actual predeclaration IDs before alias
expansion, including local TypeAlias declarations. Public transparent aliases
are checked using neutral formal arguments, so a private target named by the
declaration is rejected without confusing a caller's private generic argument
with exported declaration evidence. The check walks nested lowered type shapes;
it never marks the target public and an empty result is not positive permission.
Declaration-owned bounds and defaults are checked in a saved/restored formal
frame; defaults see only earlier formals. A transient validation context checks
the selected private declaration before transparent expansion erases its ID.
It does not yet replace full exported-signature access validation or prove
eligibility for Unknown, scoped or default-folder targets.

An explicitly written selective import also rejects its actually bound symbol
when exact source intent is `pri` and the declaring physical file differs from
the requester. Internal dependency registration does not invoke that boundary.
Namespace, glob, late lookup and containing-type paths still require the full
selected-binding consumer; this negative check does not claim those are done.
Explicit selective imports now retain the actual registration branch category
before transparent alias expansion. The negative check consults that typed
authority, so a private alias sharing a public target's canonical symbol is
rejected independently of the target's publicity. Namespace, glob and late
source uses still require their selected alias binding's declaration authority.
Authored frontend/HIR regressions cover public alias to pri Target, nested
private targets, private defaults/bounds/intermediate aliases, neutral formal
shadowing, caller-private generic arguments, public targets and direct
selective import of pri Target. All remain UNRUN.

The registration memo retains the actual selected category alongside its scalar
key. Its identity includes registry generation, write scope, found binding scope,
selected symbol ID and per-spelling mutation version. Recording happens after
registration's writes. Warm reads reuse the category; same-ID rebinding, lexical
shadowing and unbind tombstones cannot reuse a stale entry. Module reset and
registry-generation changes clear the category owner with the existing memo.
This is selection evidence; full route receipts and permission grants remain
separate, unfinished work.

## Frozen manifest inputs

ModuleSurface construction deep-copies the producer's completed evidence,
including every policy array, into a registry-owned reference. Explicit
promotion roots retain the read records, policy objects, scalar text and array
children. The complete-chain validator checks source/snapshot/root joins,
ordered immediate-to-family ancestry, positive policy SHA/provenance and child
array alignment; it does not manufacture authenticated inventory authority.
The frozen semantic digest now includes positive and negative observations,
parser/configuration provenance, exact child target inputs and existing friend
plus internal-export inputs. Incomplete evidence remains explicitly incomplete;
hashing it is not an access grant. Invalid complete evidence is uncacheable.

The configured import owner still needs exact module-child traversal receipts.
A matching physical child target is insufficient to select a public route when
another private alias reaches that same target. Actual module binding selection
must retain those hops before the requester consumer can authorize crossing a
closed interface. The manifest parser's lexical module label is not that route
identity. Selected symbol/export chains already retain their actual typed
predecessors; module routes and source-use receipts remain separate work.

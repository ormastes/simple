# Duplicate enum-provider method omits inverse owner registration

Status: confirmed duplicate source definition; local draft correction;
focused runtime regression **UNEXECUTED**.

Latest fetched release examined:
`b38c6ec4504cd5ca7da8626c974835b68734b426` (`origin/release/1.0.0`).
`declaration_providers_v1.spl` defines the same
`register_provider_enum_from_declarations_v1` signature at lines 807 and 912.
The first body publishes `reindex_enum_variant_owners(enum_def.name, [], names)`
at line 910; the second omits that call and its cycle-52 explanation. The local
draft inherited both definitions before this correction.

The duplicate is consequential wherever method registration retains the later
definition: compact provider enums then populate forward variant tables but
not the inverse owner index used by unresolved qualified constructors. This
is a source applicability finding, not executed proof of that dispatch on the
current compiler and not attribution of an existing native failure.

The correction removes only the stale second definition, retaining the first
complete body. The new `provider_enum_variant_owner_spec.spl` calls the actual
provider API and checks unique, repeated and ambiguous inverse owners. Existing
`enum_variant_owner_inverse_index_spec.spl` covers the ordinary HIR declaration
route but did not cover compact provider registration.

The initial draft changed no frozen bootstrap input. After Astra's focused
source review found zero confirmed P0/P1, the waiting scheduler was stopped
(no compiler had launched) and this four-file fix was applied to the isolated
release-fix branch. The release's retained first body, including its newer
type-parameter registration call, remains unchanged. Tests are UNEXECUTED and
no fix has landed. Source identities must be refreshed before resuming Phase 3;
landing still requires the user's link/Hello gate and exact-head Astra review.

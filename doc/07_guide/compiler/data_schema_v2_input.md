# Dedicated logical schema input V2

Status: structural API authored; runtime qualification pending. There is no new
CLI/config option advertised by this guide. Full build-envelope integration is
tracked as W1b in the [program matrix](../../08_tracking/data_attributes_program_progress_2026-11-07.md).

`data_schema_decls_from_sdn_v2(source, path, owner)` normalizes a dedicated
schema-input document into explicit views and declarations. The caller supplies
its already-authorized build/module owner. Feed those values, plus the existing
tree authority and alias table, to `data_schema_resolve_v2`. Constructed SPL input
uses the same contracts and resolver; frontend extraction is pending.

```sdn
data_policy:
    schema: simple.data-policy/v2
    declarations:
        binary:
            tree: compiler.ast
            view: compiler.ast.Binary
            attributes:
                source_span:
                    type: compiler.SourceSpan
                    required: true
                    property:
                        kind: stored
                        visibility: public
                        writable: false
                        phase: core
                        read_effects: []
                        write_effects: []
        empty:
            tree: compiler.ast
            view: compiler.ast.Empty
            attributes: {}
```

The root accepts only `data_policy`; that mapping accepts only `schema` and
`declarations`. Each declaration accepts `tree`, `view`, `attributes`. A fieldless
view requires the explicit empty attributes mapping. Each attribute accepts
`type`, optional flat nominal `args`, `required`, scalar `default`, and `property`.
Required and default cannot both be specified. Names must be canonical dotted
identifiers supplied by their semantic owner; this adapter does not resolve imports.

| Property key | Contract |
|---|---|
| `kind` | Required `stored`, `computed`, or `forwarded` |
| `visibility` | Required `public`, `module`, or `owner` |
| `visibility_owner` | Required canonical restriction key for module/owner visibility; absent/empty for public |
| `writable` | Required boolean |
| `mutation_owner` | Canonical authority key when writable; absent/empty when read-only |
| `getter`, `setter` | Computed accessor symbols; setter required iff writable |
| `forward_attr` | Forwarded property's same-schema target; no getter/setter |
| `phase` | Required canonical semantic phase key |
| `read_effects`, `write_effects` | Required explicit lists of canonical effect names, including explicit empty lists |
| `dependencies` | Optional list of same-schema attribute dependencies; forwarding target is included automatically |

Computed/forwarded declarations use `required: true`, with no default; this means
readiness must be checked by a future consumer, not that they have initializer
bits. Stored fields may be required, optional, or defaulted. A dependency must
exist in every applicable view, forwarding preserves exact type, and dependency
cycles are rejected. Property semantics must agree across views.

The adapter rejects unknown/unsupported keys, duplicate keys and unsupported
versions. Trace/rules/full-project settings belong to their existing owners and
are not accepted inside this dedicated input. Documents are bounded to 16 MiB,
4096 view declarations, 16384 attribute declarations and 256 names per
effect/dependency/input-argument list. Canonical name length is at most 4096 bytes.
Default expression text is bounded to 64 KiB; explicit authority-owner lists are
bounded to 4096 entries.

Use the outer V2 digest for V2 semantic identity. The embedded V1 projection digest
excludes new property/view meaning and is not a replacement. Keep source locations
for diagnostics; provenance/order changes alone do not change semantic identity.
No document field grants runtime access, proves effects safe, executes a default,
selects a layout or enables a trace provider.

# Rich schema input V3

Status: structural API authored; execution and frontend/config integration
qualification pending. This describes a dedicated API input, not a new CLI flag.

Call `data_schema_unbound_from_sdn_v3(source, path, owner)` to normalize a dedicated
`simple.data-policy/v3` document. The result retains full **unbound** language type
syntax. Bind it using the existing language parser/semantic owner in the explicit
compilation/module context, then construct `DataAttrDeclV3` and call
`data_schema_resolve_v3(authority, views, decls)`. Configuration cannot authorize
its own owner, synthesize a type key or bypass import/type checking.

```sdn
data_policy:
    schema: simple.data-policy/v3
    declarations:
        binary:
            tree: compiler.ast
            view: compiler.ast.Binary
            attributes:
                result:
                    type: "Result<compiler.Box<[i64]>, text>"
                    required: true
                    property:
                        kind: stored
                        visibility: public
                        writable: false
                        phase: core
                        read_effects: []
                        write_effects: []
```

The type spelling illustrates a parser input, not proof that its names bind in an
arbitrary module. V3 has no `args` key: full nested type syntax stays together.
The [V2 property/input guide](data_schema_v2_input.md) defines the remaining
property, authority, explicit-view and refusal rules. V2's version and flat
nominal API remain available with unchanged semantics.

`DataSchemaSurfaceV3` contains `contract_version`, `tree`, typed `attrs`, explicit
`views`, shared `properties`, and `schema_digest`. Use this complete V3 surface
and outer digest for V3 contexts. A type identity stores the full validated
semantic descriptor; a local ID or hash alone never proves type equality.

The decoder caps unbound type expression text at 64 KiB UTF-8 bytes. Existing
document/count/default/effect/dependency bounds still apply. Unknown keys, wrong
versions, duplicate keys, malformed shapes and legacy `args` are diagnostics.
No input field executes an accessor/default, proves effects safe, publishes a
node, chooses a storage layout or enables XRay.

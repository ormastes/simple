# Native SCV configuration API v1

Implementation status: component source and specs authored; runtime qualification and CLI/provider activation pending. The [detail design](../../05_design/scv_config_v1.md) records exact support and restrictions.

Use `std.scv.scv_config_v1.scv_config_load_v1(root, limits)` to load required repository intent plus its route table. Supply `SdnStrictLimitsV1` from `std.common.sdn.strict_types_v1`. Missing files, malformed SDN, typos, unsupported versions and bounds violations return `Err`; the loader writes nothing. Existing Windows beneath-open support is unavailable and fails closed.

Frozen object readers can instead call `scv_config_parse_v1(config_bytes, limits)`, followed by `scv_config_attach_routes_v1(config, route_bytes, limits)`. These preserve caller limits and retain exact source SHA-256 separately from any effective digest. `validated=true` means schema validation, not old-policy approval or executable availability.

Pass the separately admitted old configuration to `std.scv.scv_config_routes_v1.scv_config_route_v1(accepted, path)` and `scv_config_route_transition_v1(accepted, old_path, new_path, bound_old_domain)`. Both rename paths use old rules; a proposed routing edit cannot approve itself. Unknown roles remain conflicts. Complex overlap declarations that cannot prove disjointness reject conservatively.

Pass explicit host/old-policy/local/CLI `ScvAuthorityConstraintsV1` values to `std.scv.scv_config_effective_v1.scv_config_effective_v1`. Its returned permission constraints cannot grant anything denied by an upper layer. `canonical_sha256` binds typed settings, routes and all constraint inputs; it never substitutes for a policy acceptance or provider artifact receipt.

Old repositories may choose `scv_config_legacy_v1()` only through an explicit caller profile decision. Its `validated` is always false. A failed required-native load must never be reported as validated legacy success. Preserve ordinary saves/private checkpoints while blocking verified promotion where configuration is unavailable.

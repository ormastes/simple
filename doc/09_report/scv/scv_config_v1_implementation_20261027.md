# SCV configuration implementation lane

- Owner: Codex agent `/root/impl_configuration`.
- Worktree: `/tmp/simple-scv-impl-config-20261027`.
- Branch: `work/scv-impl-config-20261027`.
- Base: `25cdeee5d5da8f8c7c3ab530d43bc2fd4a360d26`.
- Target: `release/1.0.0` via parent integration; no push/PR/merge in this lane.
- Scope: SCVN-C01/C02/C03 configuration schema, bounded native SDN loader, semantic routing, authority intersection, focused specs/manual.
- Runtime validation: `not_run`; parent runtime-discovery owner must supply admitted binary. No seed fallback, bootstrap, tests, checks, or docgen authorized in this lane yet.
- Host integration: pending parent-owned CLI/provider wiring.

## Source candidate and caller contract

Implementation authored: six `src/lib/scv/scv_config*_v1.spl` modules, plus the approved narrow `read_only_file_view_read_beneath_bounded_v1` extension in `src/lib/common/io/read_only_file_view.spl`. No compiler, runtime C, store, database schema, file-buffer or CLI files changed.

The parser API is exactly `scv_config_parse_v1(bytes: [u8], limits: SdnStrictLimitsV1) -> Result<ScvConfigV1, text>`; it calls `sdn_parse_strict_bytes_v1` without changing limits. `scv_config_load_v1(root: text, limits: SdnStrictLimitsV1) -> Result<ScvConfigV1, text>` reads both required native config and its declared routes. Frozen-object callers can compose `scv_config_parse_v1` with `scv_config_attach_routes_v1`. Import the facade from `std.scv.scv_config_v1`.

Parent caller flow: load/parse intent; resolve immutable accepted inputs and old policy separately; call `std.scv.scv_config_routes_v1.scv_config_route_v1(accepted, path)` or `scv_config_route_transition_v1(accepted, old_path, new_path, bound_old_domain)`; compute `std.scv.scv_config_effective_v1.scv_config_effective_v1(config, host, old_policy, local, cli)` with separately supplied constraints. No return value is a publication authorization or accepted-policy receipt. Parent owns `config_commands.spl` and command dispatch/tests, outside this commit.

Review-driven containment repair: final-component no-follow was insufficient. The approved IO extension uses existing `runtime_file_view` descriptor-relative, per-component no-follow owner and exact descriptor-buffered read, with metadata size checked before allocation and close attempted on every opened path. It uses no fictional snapshot identity and makes no immutable/atomic generation claim. Windows explicitly refuses unsupported containment. Root ancestry outside the caller-admitted root remains the caller's responsibility. No new native ABI or C changes were necessary.

## Authored verification and evidence status

- Unit config spec: 18 scenarios covering exact master sample, duplicate/unknown/missing fields, unsupported version/value, malformed input, invalid UTF-8, bounds, enum/resource safety, typed roles, globs, ambiguous declarations, protected role transitions, capability/set/budget intersection, exact raw and canonical digest separation.
- Shared IO spec: 5 scenarios covering actual bounded size/bytes/empty, nonregular/traversal/missing, final and intermediate symlinks, invalid limits, and success/error cleanup beyond the 1024-handle runtime pool.
- System component spec: 6 scenarios calling the actual file loader → strict parser → schema → routes/effective owner, preserving rejected draft bytes and prior parsed values. Includes intermediate `config/` symlink refusal.
- Manual: authored outline explicitly marked not_run, not a generated execution artifact. The matching design/guide/test plan state runtime and host-integration gaps.
- Static review: `git diff --check` passed for the tracked owner extension before staging. Owned source modules are under 800 lines each. This is source-review evidence only.
- Runtime checks/tests/docgen/SSpec maintenance/core/MCP smoke: **not_run**, as instructed pending admitted-runtime discovery. No coverage percentage, pass count or full AT-C acceptance is claimed.

## Exact remaining scope

SCVN-C01/C02/C03 remain partial toward the full SCV goal. C04 manifest/profile/lock artifact resolution and exact ABI/runtime pins are not implemented here. Provider IDs are intersected symbolically, not admitted artifacts. The loader retains all eight sample sections as validated intent but does not activate capture/storage/database/gateway/execution owners or assert their operational support. Unsupported requested deviations explicitly reject: structural delta depth above zero, private transcript recording, LLM proposals, scalar timestamp winners, secure downgrades, unverified fast-hash matches, raw-copy/root retention disabling, nested pools, mandatory grammar downloads, native shared authority, unsupported enums and unknown fields. Complex wildcard pairs without provably disjoint literal prefixes/suffixes reject conservatively; ranked specificity, explicit overlap composition and authorized role-change installation are not implemented. Policy acceptance and immutable two-file generation binding remain Publisher/caller responsibilities.

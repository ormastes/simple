# Lane P8 — LLM Security Profile Registry

## Goal
Master-plan §17 / tranche item 16 (§24.16): a versioned LLM CLI security
profile registry implementing `effective = system_ceiling ∩ user_ceiling ∩
(base ∪ overlays) − denies`, deny always wins, profiles never merge by
unrestricted union. Bounded first increment: pure policy model only (no
kernel coupling, no `extern fn`, no file IO).

## Model summary
`src/os/security/llm_profiles/profile_registry.spl`:
- `LLM_RIGHT_*` — 10 independent i64 bitmask constants (own namespace, not
  imported from `capability_types.CAP_RIGHT_*`): FS_READ, FS_WRITE, FS_EXEC,
  NET, PROCESS_SPAWN, SECRETS, UI_CLIPBOARD, UI_SCREENSHOT, DEVICE,
  MODEL_ACCESS, plus `LLM_RIGHT_NONE`/`LLM_RIGHT_ALL`.
- `struct LlmProfile` — name, version, coarse `rights: i64` bitmask, plus
  refinement lists/caps: `fs_read_roots`/`fs_write_roots`/`fs_exec_roots`
  (prefix-matched paths), `net_hosts`/`secrets_labels` (exact-or-`"*"`
  matched), and five numeric resource caps (cpu/mem/wallclock/cost/tokens).
- `struct LlmDenyList` — `deny_rights` bitmask + `deny_fs_paths`/
  `deny_net_hosts`/`deny_secrets_labels`, applied last and unconditionally.
- `resolve_effective(system_ceiling, user_ceiling, base, overlays, denies) ->
  LlmProfile` — three-step law: (1) union base rights/lists with every
  overlay's (overlays only ever ADD before ceiling clamp); (2) intersect the
  rights bitmask against `system_ceiling.rights & user_ceiling.rights`, and
  filter every list to entries covered by BOTH ceilings; resource caps take
  `max(base, overlays)` then `min` against both ceilings; (3) subtract
  `denies` unconditionally last (deny always wins), then gate every
  refinement list by its governing bit (`_gate_list_by_right`) so a closed
  dimension carries no roots/hosts/labels regardless of list contents.
- `is_subset(child, parent) -> bool` — `(child & parent) == child`, the
  bitmask attenuation check, exported and reused internally.
- `has_right(rights, bit) -> bool` — single-bit convenience over `is_subset`.
- Six built-in profile functions (never module-level array/const — the
  runtime landmine noted in the task): `profile_offline`,
  `profile_code_review`, `profile_workspace_write`,
  `profile_network_research`, `profile_build_and_test`,
  `profile_system_administration`, plus `profile_by_name(text) ->
  LlmProfile?` (plain if/elif chain, no Dict, nil for unknown).

## Spec verdict
`test/01_unit/os/security/llm_profile_attenuation_spec.spl` — 5 describe
blocks, **18 examples, 0 failures** (`4 + 3 + 2 + 5 + 4`), run via:
```
mkdir -p /tmp/p8lane/bin
cp bin/release/x86_64-unknown-linux-gnu/simple /tmp/p8lane/bin/p8job
cp src/compiler_rust/target/bootstrap/simple /tmp/p8lane/bin/simple_seed
timeout 240 /tmp/p8lane/bin/p8job run test/01_unit/os/security/llm_profile_attenuation_spec.spl
```
Coverage: (a) deny wins over a rights-bit grant, over an overlay re-grant,
over a filesystem path grant, and over a net-host grant; (b) effective rights
proven a subset of the system ceiling AND independently of the user ceiling
via `is_subset`, plus effective fs roots proven covered by both ceilings; (c)
a base+overlay union of 292 (FS_EXEC|SECRETS|DEVICE) against ceilings whose
intersection is only 4 (FS_EXEC) resolves to exactly 4, and two distinct
overlay profiles combined never exceed the ceiling intersection; (d)
`is_subset` correctly flags a genuine violation (child holds NET, parent
holds only FS_READ) plus reflexivity/empty-set edge cases; profile-registry
sanity (all six built-ins resolve by name, unknown name -> nil, offline
grants nothing, system-administration is still clamped by a narrow ceiling).

**Fail-once proof (per task instruction):** temporarily deleted the
`& (~denies.deny_rights)` subtraction in `resolve_effective` (BREAK-TEST
comment), reran — 2 failures in the "deny always wins" group as expected
(`expected 11 to equal 3`, `expected true to equal false`), all other groups
stayed green. Restored the original line via backup diff (confirmed
byte-identical), reran — back to 18 examples, 0 failures.

## Next increment (resume plan — do NOT modify cspace_spawn.spl)
Wire `resolve_effective()`'s output into `SpawnSpec`/`CapGrant` construction
at spawn time:
1. A new adapter (separate file, e.g.
   `src/os/security/llm_profiles/profile_to_spawn_spec.spl`) that maps an
   `LlmProfile.rights` bit + refinement lists to concrete
   `os.kernel.types.capability_types.CapabilityKind` values (e.g.
   `LLM_RIGHT_FS_READ` + each `fs_read_roots` entry -> one
   `CapabilityKind.FileRead(path_prefix: ...)`) and emits a `[CapGrant]` list
   using `atten_identity()`/`atten_rights()` from `cspace_spawn.spl` — read
   only, no edits to that file.
2. Contract spec (owned by P8, run by P2 per the parallel-plan cross-lane
   contract convention) proving: a profile's `LLM_RIGHT_FS_WRITE` bit maps to
   a `CapabilityKind.FileWrite` grant with the SAME path roots the profile
   resolved to, and a profile that denied a dimension produces NO grant for
   it (so `spawn_with_cspace`'s own monotonic guard is defense-in-depth, not
   the only gate).
3. Audit-record emission (§17 "Every tool call passes policyd... Audit
   record") is out of scope for this increment — needs the policyd
   normalize/evaluate/approve pipeline from a later tranche item, not just
   the registry.
4. Consider whether `LlmProfile.version` should participate in signed/atomic
   rollback (§17 lifecycle: "versioned, signed, atomic, rollback, SDN
   import/export, diff UI, simulation, explain-denial, expiration") — SDN
   import/export of `LlmProfile`/`LlmDenyList` is unimplemented; this
   increment kept profiles as function-returning constants per the task's
   explicit instruction to avoid module-level array initializers.

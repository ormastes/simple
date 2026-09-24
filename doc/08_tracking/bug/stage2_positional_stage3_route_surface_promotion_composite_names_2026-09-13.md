# Site 19: Stage-2 positional Stage-3-route probe fails — surface promotion `composite_names` (macOS, 2026-09-13)

- Status: FIXED (2026-09-13) — regression of `460aa9781cc` reintroduced by `db127a8e8c4`; see the root-cause section at the end
- Area: `bootstrap_stage2_positional_stage3_route` capability probe / module
  surface registry graph promotion (`src/compiler/20.hir/hir_lowering/module_surface_registry.spl`)
- Found by: macOS lane F72 run 34, worktree `agent-a0e562ca3e5681c38`, tip
  `c1329f766a2` (carries PR #898, the site-18 fix), `--stop-after-stage2
  --full-bootstrap --mode=dynload --jobs=half`
- Blocks: Stage-2 admission. The frontend sanity smoke now PASSES on both
  bootstrap legs (site 18 cleared); this is the next probe.

## Symptom (verbatim, `stage2-receiver.log`)

```
error: stage2 failed the positional pure-Simple Stage-3 route (status 1)
error: in-process native-build: Module surface registry graph promotion failed after phase 2: field composite_names of surface[0] logical=<worktree>.scripts.check.cert.redeploy_gate.fixtures.stage2_module_path_naming canonical=<same> package=<worktree>.scripts.check.cert.redeploy_gate.fixtures (scope sentinel promote=true, surfaces=2)
```

Rejected candidate: `.simple/storage/build/bootstrap/stage2-rejected/aarch64-apple-darwin/simple`,
139,504,696 B, sha256 `70f1a6517183d74c1a855f4761235dd2c62d52a63bfa3c36f7c5fb53b83f2703`.

## Relation to the existing records

`stage2_module_surface_registry_graph_promotion_failed_2026-09-13.md` (FIXED by
`460aa9781cc` / `592041db98a`, Linux BOOT-7) and
`stage2_sanity_module_surface_registry_promotion_fails_2026-09-13.md` (CLOSED as
already fixed) describe the same gate. This tree carries both fixes, and the
failing field is `composite_names`, so this is a different instance, not a
regression of those. Not root-caused here: it is unrelated to the K1 admission
lane that exposed it, and a wrong guess would cost a 60-minute Stage-2 rebuild.
Reproduce cheaply first: run the rejected candidate on
`scripts/check/cert/redeploy_gate/fixtures/stage2_module_path_naming.spl` with the
probe's argv from `scripts/check/cert/redeploy_gate/candidate_frontend_admission.shs`
(positional entry, `--mode one-binary`).

## Root cause and fix (2026-09-13, F73) — FIXED

Status: FIXED. Not a new instance and not a seed miscompile: a **regression of
`460aa9781cc`**, reintroduced by `db127a8e8c4` (PR #873) nine hours later.

`460aa9781cc` had measured, with gdb on a Stage-2 candidate, that the premise
"a second `rt_transient_heap_promote` answers true only for a value still owned
by the dying scope" is false, and deleted the post-condition resting on it from
`module_surface_promote_freeze_names`. `db127a8e8c4` reinstated that
post-condition — reasoning from the very docstring `460aa9781cc` had disproved,
and self-described in its own message as "NOT YET VERIFIED end to end" — and
newly applied it to all 24 retained fields through a new
`module_surface_promote_field(failure, label, value)` helper. It left
`460aa9781cc`'s regression spec unrun; that spec has been RED at **2 of 3
examples** on `origin/main` ever since.

Why it is red by construction for these fields, from the C runtime rather than
inference: `rt_transient_heap_promote` returns 1 whenever classification and the
plan walk succeed. For a transient heap STRING the first promote clears
`RT_CORE_STRING_FLAG_TRANSIENT` (runtime_native.c:2474), so
`rt_core_transient_classify` (:2362) then answers "untracked", the root
`classify(...) == 1` test fails and the second promote answers false — the only
case the premise covers. Every field in the 24-field loop is an ARRAY: promote
merely zeroes `transient_scope_id` (:2493), and classify consults neither that
nor the raw-allocation owned bit, so a registered array classifies as tracked
and the repeat promote answers **true forever**. The guard therefore fired on
the first field of the first surface — `field composite_names of surface[0]` —
which is exactly the verbatim symptom above.

Fix: delete `module_surface_promote_field` and the per-field verdict; promote
the 24 fields as a flat statement sequence, and restore
`module_surface_promote_freeze_names` to `460aa9781cc`'s guard-free form.
Fail-closed coverage is unchanged in substance: the registry root carrier is a
freshly built `[Any]` whose promote verdict IS meaningful and still returns a
named reason, and the driver runs `module_surfaces_retained_alignment_error`
after `_sffi_transient_array_scope_end()` — the real post-condition, at the only
moment it means anything.

Tests: `module_surface_freeze_names_promote_guard_spec.spl` 3 examples / 2
failures → **4 examples / 0 failures** (a fourth example now pins the array-field
loop the same way; sabotage-verified — reintroducing
`fn module_surface_promote_field(` turns it RED at 1 failure).
`module_surface_promote_reason_spec.spl` retargeted off the deleted route,
**4 examples / 0 failures**.

Interpreter-vs-native note: the usual discriminator does **not** apply here. The
Rust seed's interpreter stubs the transient-scope externs, so the guard cannot
fire under the interpreter at all — an interpreter "pass" is vacuous, not
evidence of a seed miscompile. The authority is the C runtime source plus
`460aa9781cc`'s gdb measurement.

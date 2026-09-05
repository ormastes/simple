# Lane INT-3 — LLM profile -> spawn effective-rights adapter

**Program:** SimpleOS production harden — master plan §5.4 + §17
**Status:** Adapter + spec landed. NOT wired into cspace_spawn.spl (deliberately
out of scope this increment).

## Gap this lane closed

`profile_registry.spl` (LlmProfile, LLM_RIGHT_* i64 bitmask,
`resolve_effective`) and `spawn_authority.spl` (CAP_RIGHT_*-space u32 spawn
rights, `spawn_effective_rights`, `spawn_rights_is_subset`) did not talk to
each other. A resolved LLM profile had no path into the spawn-time capability
rights a child process actually receives. This lane adds the pure adapter that
maps one into the other, so a future spawn call site can compute:

    llm_spawn_effective_rights(resolved_profile, parent_delegable, executable_ceiling)

and get back a u32 CAP_RIGHT_*-space mask that is provably a subset of the
profile's own mapped rights, of `parent_delegable`, and of
`executable_ceiling` — deny-by-omission, never amplified.

## New file: `src/os/security/llm_profiles/profile_spawn_adapter.spl`

Pure functions, no `extern fn`, no IO:

- `llm_profile_to_spawn_rights(profile: LlmProfile) -> u32` — maps
  `profile.rights` (LLM_RIGHT_* i64) into the CAP_RIGHT_* u32 spawn rights
  space per the table below.
- `llm_spawn_effective_rights(profile: LlmProfile, parent_delegable: u32, executable_ceiling: u32) -> u32`
  — `llm_profile_to_spawn_rights(profile) & parent_delegable & executable_ceiling`.
  Pure intersection, no union anywhere.
- `llm_spawn_rights_triple_attenuated(profile, parent_delegable, executable_ceiling) -> bool`
  — invariant oracle reusing `spawn_authority.spawn_rights_is_subset` three
  times (vs. the profile's own mapped rights, `parent_delegable`, and
  `executable_ceiling`).

## The mapping table (LLM_RIGHT_* -> CAP_RIGHT_*)

CAP_RIGHT_* (`capability_types.spl`) is a generic kernel object-capability
rights space (READ/WRITE/EXEC/ADMIN/MOUNT/QUEUE_SUBMIT/MAP/DATASET_BUILD/
QUEUE_RECV) shared by file/block/storage/mount/queue capabilities. LLM_RIGHT_*
is a product-policy space. The two are not isomorphic, so the mapping is
deliberately conservative and fail-closed: only a bit with a genuine
kernel-capability analogue is mapped.

| LLM_RIGHT_*             | value | -> CAP_RIGHT_*     | value | rationale |
|--------------------------|------:|---------------------|------:|-----------|
| FS_READ                  |     1 | CAP_RIGHT_READ       |     1 | direct match |
| FS_WRITE                 |     2 | CAP_RIGHT_WRITE      |     2 | direct match |
| FS_EXEC                  |     4 | CAP_RIGHT_EXEC       |     4 | direct match |
| NET                      |     8 | **NONE (0)**         |     — | no kernel CAP_RIGHT bit for network I/O (mediated by a higher-layer socket/proxy object not in capability_types.spl) |
| PROCESS_SPAWN            |    16 | **NONE (0)**         |     — | spawn authority is governed by the separate spawn_authority/cspace_spawn gate, not a CAP_RIGHT bit on an unrelated resource |
| SECRETS                  |    32 | **NONE (0)**         |     — | no kernel CAP_RIGHT bit for a secrets store |
| UI_CLIPBOARD             |    64 | **NONE (0)**         |     — | no kernel CAP_RIGHT bit for UI clipboard |
| UI_SCREENSHOT            |   128 | **NONE (0)**         |     — | no kernel CAP_RIGHT bit for UI capture |
| DEVICE                   |   256 | CAP_RIGHT_MAP        |    64 | device access needs MMIO/device-memory mapping rights — closest analogue |
| MODEL_ACCESS             |   512 | **NONE (0)**         |     — | product-policy concept, no kernel object right |

Unmapped bits fall through to 0 by construction (accumulator starts at 0u32,
only the four `if`s above ever set a bit — no `else` branch can leak an
unknown/future bit through).

Derived built-in mappings:
- `profile_offline()` (LLM_RIGHT_NONE=0) -> spawn rights `0u32`.
- `profile_system_administration()` (LLM_RIGHT_ALL=1023, all 10 bits) -> spawn
  rights `CAP_RIGHT_READ|WRITE|EXEC|MAP = 71u32` (the broadest this mapping
  table can ever produce — NET/PROCESS_SPAWN/SECRETS/UI_*/MODEL_ACCESS being
  set contributes nothing).

## Spec: `test/01_unit/os/security/llm_profile_spawn_adapter_spec.spl`

4 describe blocks / 9 `it` examples:
1. Triple attenuation — concrete bit-value proof + `llm_spawn_rights_triple_attenuated` oracle.
2. Profile itself is a ceiling — a right absent from the profile never appears
   even with wide-open parent + executable.
3. Unmapped LLM rights (NET, PROCESS_SPAWN) fail closed to zero spawn rights,
   individually and combined, even through wide-open ceilings.
4. Built-in profile ordering — offline (0) vs system-administration (71,
   clamped down to a narrow `parent_delegable` of 3 in the test).

### Verdict

```
2 examples, 0 failures   (Group 1: triple attenuation)
1 example, 0 failures    (Group 2: profile-lacks-right)
3 examples, 0 failures   (Group 3: unmapped fail-closed)
3 examples, 0 failures   (Group 4: offline vs system-administration)
```
Total: **9 examples, 0 failures.** Run via
`/tmp/int3/bin/int3job run test/01_unit/os/security/llm_profile_spawn_adapter_spec.spl`
(deployed `bin/simple` is a stale seed per repo convention; `int3job` is a copy
of `bin/release/x86_64-unknown-linux-gnu/simple`).

**Fail-once proof performed:** temporarily changed
`llm_spawn_effective_rights`'s body from
`profile_spawn_rights & parent_delegable & executable_ceiling` to
`profile_spawn_rights | parent_delegable | executable_ceiling` (intersection
-> union) and re-ran the spec: 5 of 9 examples failed (the triple-attenuation
group, the profile-ceiling group, one fail-closed example, and the offline-vs-
sysadmin clamp example — the ones with a non-trivial mask relationship). This
confirms the spec is not vacuously green. The change was then reverted and the
suite re-confirmed at 9/9 green before finishing.

## Next increment (resume plan — NOT done here)

Wire `llm_spawn_effective_rights` into the real spawn syscall path:

1. At the call site that currently builds a `SpawnSpec`/`CapGrant` for an
   LLM-driven child (loader spawn path, likely near where
   `spawn_authority.spawn_spec_effective_rights` is invoked), first resolve
   the LLM profile (`profile_registry.resolve_effective`) to get an
   `LlmProfile`, then call `llm_spawn_effective_rights(resolved, parent_delegable, executable_ceiling)`
   to get the u32 CAP_RIGHT_* mask, then fold that mask into the
   `AttenuationSpec.rights_mask` (or an equivalent explicit denial) so the
   `CapGrant`s actually minted for the child are bounded by it.
2. Decide whether `llm_spawn_effective_rights` needs an `explicit_denials: u32`
   parameter (mirroring `spawn_authority.spawn_effective_rights`'s last
   argument) once a concrete deny-list call site exists — this increment
   intentionally left denial-by-omission only (intersection-only, no separate
   subtraction step) since the task scope did not require a denial-list
   integration test yet.
3. Extend the mapping table if `capability_types.spl` grows a NET/SPAWN/
   SECRETS-shaped capability kind — today those LLM_RIGHT_* bits are
   correctly-but-permanently fail-closed until such a kernel object exists;
   revisit rather than force a weak analogy.
4. Add an integration spec once (1) lands, proving an end-to-end
   `resolve_effective` -> `llm_spawn_effective_rights` -> minted `CapGrant`
   chain never grants what `resolve_effective`'s own `is_subset` check would
   reject.

Do NOT touch `profile_registry.spl`, `spawn_authority.spl`, or
`cspace_spawn.spl` to do (1)-(4) — those are other lanes'/owners' files; this
lane's adapter is the seam they should import from.

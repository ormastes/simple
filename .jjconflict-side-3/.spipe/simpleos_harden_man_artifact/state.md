# Lane MAN — unified SimpleArtifactManifest (master plan §5.3 + §24.8 groundwork)

**Status:** typed contract + spec landed in the working copy (NOT committed).
**Date:** 2026-07-27
**Plan:** doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane MAN)
**Design:** doc/01_research/domain/simpleos_production_host_master_plan.md §5.3, §5.4, §12

## Files (exclusive to this lane)

| Path | Role |
|------|------|
| `src/os/kernel/loader/artifact_manifest.spl` | the typed `SimpleArtifactManifest` + pure policy functions (new, 430 lines) |
| `test/01_unit/os/kernel/loader/artifact_manifest_spec.spl` | absolute-oracle contract spec (new, 26 examples) |
| `.spipe/simpleos_harden_man_artifact/state.md` | this file |

Nothing else was touched. `fs_exec_resolve.spl`, `fs_exec_spawn.spl`,
`spawn_authority.spl`, `syscall_process.spl` were READ ONLY.

## The manifest fields (§5.3, all present)

`SimpleArtifactManifest`:
`format_version`, `artifact_kind`, `target` (`ManifestTarget{os,arch,abi}`),
`entrypoint`, `required_abi_features`, `required_services`,
`required_capabilities` (u32 rights mask), `resource_limits`
(`ManifestResourceLimits{max_memory_bytes,max_open_handles,max_threads,cpu_budget_us}`),
`namespace_template`, `native_libraries`, `smf_libraries`, `interpreter`,
`argument_schema` (`[ManifestArgument{name,value_kind,required,default_value}]`),
`startup_preloads`
(`[ManifestPreload{source_arg,fixed_path,mode,required,maximum_bytes,access,prefault,hash_policy}]`),
`content_hashes`, `signature`, `debug_identity`.

Artifact kinds: `elf` | `smf` | `script` | `native_simple`.

## Existing launch-metadata owner built on — NO second manifest (§4)

**Owner: `src/app/startup/launch_metadata.spl`** (`LaunchMetadata` +
`StartupLaunchPlan`), with its three landed on-disk encodings:
`.simple_launch.sdn` sidecar (`render_/parse_launch_metadata_sidecar`), the SMF
section-type-15 payload (`parse_launch_metadata_from_smf_bytes`), and the
`SIMPLE_LAUNCH_V1` native trailer
(`render_/parse_launch_metadata_from_native_bytes`).

How a rival format was avoided:

1. **No new encoding was written.** `artifact_manifest.spl` contains zero
   serialization — no renderer, no parser, no magic, no sidecar path. It is
   pure in-memory policy. The producer/encoding stays entirely in
   `launch_metadata.spl`.
2. **One-way adapter, not a fork.** `manifest_from_launch_metadata(...)` takes
   the fields of an ALREADY-PARSED `LaunchMetadata` (entry_kind, target_os,
   target_arch, target_abi, entrypoint, native_libraries, smf_libraries) and
   projects them into the unified manifest. Field names are deliberately
   identical so the correspondence is greppable.
   `manifest_kind_from_launch_entry_kind` maps that module's existing
   vocabulary (`native`/`smf`/`script`, from `startup_detect_launch_kind`) onto
   the §5.3 kinds (`native` -> `native_simple`).
3. **Taken as loose fields, not the struct.** The kernel loader does not
   `use app.startup.launch_metadata` — that would drag a host-side module onto
   the ring-0 path. The adapter's signature is the seam.
4. **Extension direction is recorded in the module header:** when the §5.3
   fields `LaunchMetadata` does not yet carry (rights ceiling, resource limits,
   namespace template, argument schema, preloads, hashes, signature, debug
   identity) need to be PERSISTED, they get added to the EXISTING sidecar
   renderer/parser in `launch_metadata.spl` — not to a competing format here.
5. `manifest_summary()` mirrors the shape of the existing
   `startup_feature_summary()` so serial traces stay comparable.

## Validation rules (fail closed, one distinct reason each)

`manifest_validate(m)` / `manifest_validate_for_target(m, running)` return a
plain `ManifestCheck{ok, reason}` (deliberately NOT a cross-module `Result` —
`Ok`/`Err` do not resolve inside imported method bodies). Checks are ORDERED so
no rejection is masked by a later one:

| # | Condition | reason |
|---|-----------|--------|
| 1 | `format_version != 1` | `unsupported_format_version` |
| 2 | `artifact_kind` not in the four kinds | `unknown_artifact_kind` |
| 3 | `entrypoint == ""` | `empty_entrypoint` |
| 4 | kind is `script` and `interpreter == ""` | `script_without_interpreter` |
| 5 | target triple does not match the running target | `target_triple_mismatch` |
| 6 | `signature != ""` but `content_hashes` empty | `signature_without_content_hash` |
| — | otherwise | `ok` |

Fail-closed details:
- A bare `manifest_for_kind(k)` skeleton has an EMPTY entrypoint and (for
  script) an EMPTY interpreter, so an unbound descriptor can never execute.
- An interpreter is NEVER defaulted for a script — the loader must not choose
  an interpreter for untrusted source.
- An EMPTY target field is NOT a wildcard; only the explicit literal `"any"` is.

## Rights model

- `manifest_kind_base_rights(kind)` — what the kind needs to start.
  elf/smf/native_simple = `READ|EXEC|MAP` (69). script = `READ|MAP` (65): a
  script is read and mapped, the INTERPRETER is what executes.
- `manifest_kind_allowed_rights(kind)` — the hard clamp.
  **`CAP_RIGHT_ADMIN` is absent from every kind**: no file on disk can request
  admin authority. A script additionally can never get `EXEC` or `MOUNT`. An
  unknown kind is allowed nothing (0).
- `manifest_required_rights(m)` = `(declared | kind_base | implied-by-declared-
  libraries/preloads) & kind_allowed`. The trailing clamp is what makes it a
  CEILING rather than an amplifier — feeds §5.4's
  `executable_policy_ceiling`.
- `manifest_effective_rights(m, parent_delegable, system_ceiling)` **composes
  the landed `spawn_authority.spawn_effective_rights`** (imported, not
  re-derived), with the clamped request as both the executable ceiling and the
  manifest request, and explicit denials = 0 (denials are a spawn-site
  `SpawnSpec` input, not a property of the artifact). Intersection only.
- `manifest_rights_within_ceilings(...)` self-checks the subset property via the
  landed `spawn_authority.spawn_rights_is_subset`, so "subset" means one thing
  in both modules.

## Freestanding discipline honoured (ring-0-adjacent loader code)

- Every constant list and every reason string is a FUNCTION
  (`manifest_kind_elf()`, `manifest_reason_*()`, `manifest_running_target()`) —
  no module-level `val`/`var` arrays or `[text]`, which do not run under the
  freestanding native build.
- No classes, no trait objects: plain value structs + free functions.
- Kind/target matching uses whole-string `==` on explicitly built components
  only — no `char_at`/`starts_with` (unreliable on dynamically built strings on
  the x64 freestanding path) and no text ordering (`<`/`>` is raw pointer
  compare in native codegen).
- Validation is one flat function over scalars; call depth stays shallow.
- Builders never mutate through two struct-field hops from a receiver: they
  copy-and-return, and a spec example ("builds manifests without mutating the
  input manifest") asserts the input is untouched.

## Spec verdict

```
26 examples, 0 failures
```
Runner: `timeout 300 /tmp/manlane/bin/manjob run test/01_unit/os/kernel/loader/artifact_manifest_spec.spl`
(`/tmp/manlane/bin/manjob` = copy of `bin/release/x86_64-unknown-linux-gnu/simple`;
the deployed `bin/simple` is a stale seed whose `simple test` hangs.)

**Mutation proof (the spec can fail):** the `entrypoint == ""` check in
`manifest_validate_for_target` was replaced with `if false:` and the suite
reported `26 examples, 1 failure` with exactly
`✗ rejects a manifest with an empty entrypoint` — then the check was restored
and the suite returned to `26 examples, 0 failures`.

Oracles are absolute: exact reason strings (`"empty_entrypoint"`,
`"target_triple_mismatch"`, ...), exact bitmasks (`READ=1`, `EXEC=4`,
`ADMIN=8`, `MAP=64`; elf ceiling `69`; script ceiling `65`; parent `7` &
ceiling `69` & system `77` -> effective `5` = `READ|EXEC`), and a
six-reasons-are-seven-distinct-strings check so two failures can never be
confused.

## Lint

`bin/simple lint` on the new module: **0 style warnings that are not shared
with the landed neighbour.** 5 `error[primitive_api]` ("public API uses bare
primitive `u32`/`i64`") + 2 `unnamed_duplicate_typed_args` warnings. The
already-landed `src/os/kernel/loader/spawn_authority.spl` trips **13** errors of
the same class — rights masks are `u32` by ABI necessity (they must match
`AttenuationSpec.rights_mask` in `cspace_spawn`). Not a regression introduced by
this lane; flagged here rather than silently normalized. Spec file lints clean
after converting boolean assertions to `assert_true`/`expect_not`.

## Not done in this increment (deliberate scope)

- No IO: the manifest is data. Reading one off a disk/descriptor, verifying
  `content_hashes` against real bytes, and checking the signature are later
  increments.
- No wiring into `fs_exec_resolve.spl` / `fs_exec_spawn.spl` — those are other
  lanes' files this increment must not touch.
- `argument_schema` / `startup_preloads` are carried and validated-through but
  the §12 generated arg parser and preload resolver are not built here.

## Next increment (§24.8)

**Descriptor-based execution consuming this manifest at the real spawn path.**
Sequence: `fs_exec_resolve` produces an immutable executable HANDLE (not a
path — POSIX `fexecve()` model, so a path swap between check and exec cannot
happen); `fs_exec_spawn` reads the manifest off that handle via the existing
`launch_metadata` decoders, calls `manifest_validate`, and feeds
`manifest_required_rights` into `spawn_authority`'s §5.4 intersection as the
`executable_policy_ceiling` instead of today's per-format ad-hoc decisions.

Requires: (a) coordination with the lanes owning `fs_exec_resolve.spl` /
`fs_exec_spawn.spl`; (b) extending the `launch_metadata.spl` sidecar
renderer/parser with the new persisted fields; (c) **QEMU boot evidence** —
real-firmware proxy (OVMF pflash), boot -> in-guest exec of an elf, an smf, a
script and a native-Simple artifact, with the serial transcript showing the
`manifest_summary()` line and a rejected malformed manifest; and (d) per
`.claude/rules/board-runnable.md`, a kept-alive physical-board path for the same
artifacts — a QEMU-only result would be a defect, not a completion.

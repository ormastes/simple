# Unified SimpleArtifactManifest Specification (P2 Process/Loader)

> Master plan §5.3 requires ONE artifact manifest covering ELF, SMF, script and native-Simple artifacts so the loader has a single policy surface instead of per-format ad-hoc decisions. This spec is the contract for `src/os/kernel/loader/artifact_manifest.spl`:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 31 | 31 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unified SimpleArtifactManifest Specification (P2 Process/Loader)

Master plan §5.3 requires ONE artifact manifest covering ELF, SMF, script and native-Simple artifacts so the loader has a single policy surface instead of per-format ad-hoc decisions. This spec is the contract for `src/os/kernel/loader/artifact_manifest.spl`:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-P2-ARTIFACT-MANIFEST |
| Category | Runtime / Security |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane MAN) |
| Design | doc/01_research/domain/simpleos_production_host_master_plan.md (§5.3, §5.4, §12) |
| Research | doc/01_research/domain/simpleos_production_host_master_plan.md |
| Source | `test/01_unit/os/kernel/loader/artifact_manifest_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
## Operator workflow
## Compatibility and limitations

# Unified SimpleArtifactManifest Specification (P2 Process/Loader)

**Feature IDs:** #OS-P2-ARTIFACT-MANIFEST
**Category:** Runtime / Security
**Difficulty:** 3/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane MAN)
**Design:** doc/01_research/domain/simpleos_production_host_master_plan.md (§5.3, §5.4, §12)
**Research:** doc/01_research/domain/simpleos_production_host_master_plan.md

## Overview

Master plan §5.3 requires ONE artifact manifest covering ELF, SMF, script and
native-Simple artifacts so the loader has a single policy surface instead of
per-format ad-hoc decisions. This spec is the contract for
`src/os/kernel/loader/artifact_manifest.spl`:

  - each of the four artifact kinds has a typed skeleton, and a well-formed
    manifest of that kind validates;
  - validation is FAIL CLOSED with a DISTINCT reason per failure: unsupported
    format version, unknown artifact kind, empty entrypoint, script with no
    interpreter, target-triple mismatch, signature with no content hash;
  - a script manifest with no interpreter is REJECTED, never defaulted — the
    loader must not choose an interpreter for untrusted source;
  - `manifest_required_rights` is a CEILING: no combination of declared fields
    can produce a bit the artifact kind does not allow (no kind allows
    CAP_RIGHT_ADMIN; a script can never get CAP_RIGHT_EXEC);
  - `manifest_effective_rights` is the §5.4 intersection composed from the
    landed `spawn_authority.spawn_effective_rights`, so the result is always a
    subset of the artifact ceiling, the parent's delegable rights AND the
    system ceiling — asserted with concrete bit values.

The manifest is the kernel-side typed projection of the ALREADY-LANDED launch
metadata (`src/app/startup/launch_metadata.spl`), not a second manifest format:
`manifest_from_launch_metadata` is the one-way adapter and is covered here.

Oracles are absolute (exact reason strings, exact bitmasks) — no
self-referential comparisons.

## Scenarios

### unified SimpleArtifactManifest (master plan 5.3)

#### uses the dependency-free common value contract through the loader adapter

- Verify: uses the dependency-free common value contract through the loader adapter
   - Expected: common_manifest.artifact_kind equals `elf`
   - Expected: common_manifest.format_version equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: uses the dependency-free common value contract through the loader adapter")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val common_manifest: CommonSimpleArtifactManifest = manifest_for_kind(manifest_kind_elf())
expect(common_manifest.artifact_kind).to_equal("elf")
expect(common_manifest.format_version).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### validates a well-formed ELF manifest

- Verify: validates a well-formed ELF manifest
- the elf skeleton carries elf64 + W^X abi features and app_default namespace
   - Expected: m.artifact_kind equals `elf`
   - Expected: m.format_version equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: m.namespace_template equals `app_default`
- and it validates against the running target
   - Expected: check.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: validates a well-formed ELF manifest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("the elf skeleton carries elf64 + W^X abi features and app_default namespace")
val m = _elf_ok()
expect(m.artifact_kind).to_equal("elf")
expect(m.format_version).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(m.required_abi_features).to_contain("elf64")
expect(m.required_abi_features).to_contain("w_xor_x")
expect(m.namespace_template).to_equal("app_default")

step("and it validates against the running target")
val check = manifest_validate(m)
assert_true(check.ok)
expect(check.reason).to_equal("ok")
```

</details>

#### validates a well-formed SMF manifest

- Verify: validates a well-formed SMF manifest
   - Expected: m.artifact_kind equals `smf`
   - Expected: check.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: validates a well-formed SMF manifest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = _smf_ok()
expect(m.artifact_kind).to_equal("smf")
expect(m.required_abi_features).to_contain("smf1")
expect(m.required_abi_features).to_contain("module_graph")
val check = manifest_validate(m)
assert_true(check.ok)
expect(check.reason).to_equal("ok")
```

</details>

#### validates a well-formed script manifest that declares its interpreter

- Verify: validates a well-formed script manifest that declares its interpreter
   - Expected: m.artifact_kind equals `script`
   - Expected: m.interpreter equals `/usr/bin/simple`
   - Expected: check.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: validates a well-formed script manifest that declares its interpreter")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = _script_ok()
expect(m.artifact_kind).to_equal("script")
expect(m.interpreter).to_equal("/usr/bin/simple")
expect(m.required_abi_features).to_contain("script_host")
val check = manifest_validate(m)
assert_true(check.ok)
expect(check.reason).to_equal("ok")
```

</details>

#### validates a well-formed native-Simple manifest

- Verify: validates a well-formed native-Simple manifest
   - Expected: m.artifact_kind equals `native_simple`
   - Expected: check.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: validates a well-formed native-Simple manifest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = _native_ok()
expect(m.artifact_kind).to_equal("native_simple")
expect(m.required_abi_features).to_contain("simple_rt")
expect(m.required_abi_features).to_contain("launch_meta_v1")
val check = manifest_validate(m)
assert_true(check.ok)
expect(check.reason).to_equal("ok")
```

</details>

#### knows exactly the four artifact kinds

- Verify: knows exactly the four artifact kinds
- anything else is unknown - no fuzzy prefix matching


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: knows exactly the four artifact kinds")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
assert_true(manifest_kind_is_known("elf"))
assert_true(manifest_kind_is_known("smf"))
assert_true(manifest_kind_is_known("script"))
assert_true(manifest_kind_is_known("native_simple"))
step("anything else is unknown - no fuzzy prefix matching")
expect_not(manifest_kind_is_known("wasm"))
expect_not(manifest_kind_is_known("elf64"))
expect_not(manifest_kind_is_known(""))
```

</details>

#### rejects a manifest with an empty entrypoint

- Verify: rejects a manifest with an empty entrypoint
- a bare skeleton is deliberately not yet valid
   - Expected: skeleton.entrypoint equals ``
   - Expected: check.reason equals `empty_entrypoint`
   - Expected: manifest_reason_empty_entrypoint() equals `empty_entrypoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: rejects a manifest with an empty entrypoint")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("a bare skeleton is deliberately not yet valid")
val skeleton = manifest_for_kind(manifest_kind_elf())
expect(skeleton.entrypoint).to_equal("")
val check = manifest_validate(skeleton)
expect_not(check.ok)
expect(check.reason).to_equal("empty_entrypoint")
expect(manifest_reason_empty_entrypoint()).to_equal("empty_entrypoint")
```

</details>

#### rejects an unknown artifact kind

- Verify: rejects an unknown artifact kind
   - Expected: check.reason equals `unknown_artifact_kind`
   - Expected: manifest_reason_unknown_kind() equals `unknown_artifact_kind`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: rejects an unknown artifact kind")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = manifest_with_entrypoint(manifest_for_kind("wasm"), "/usr/bin/thing")
val check = manifest_validate(m)
expect_not(check.ok)
expect(check.reason).to_equal("unknown_artifact_kind")
expect(manifest_reason_unknown_kind()).to_equal("unknown_artifact_kind")
```

</details>

#### rejects a target-triple mismatch against the running target

- Verify: rejects a target-triple mismatch against the running target
- the running target is simpleos/x86_64/simpleos
   - Expected: running.os equals `simpleos`
   - Expected: running.arch equals `x86_64`
   - Expected: running.abi equals `simpleos`
- a linux/aarch64 artifact does not run here
   - Expected: check.reason equals `target_triple_mismatch`
   - Expected: manifest_reason_target_mismatch() equals `target_triple_mismatch`
- an EMPTY target field is not a wildcard - fail closed
   - Expected: manifest_validate(blank).reason equals `target_triple_mismatch`
- but an explicit any/any/any wildcard matches


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: rejects a target-triple mismatch against the running target")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("the running target is simpleos/x86_64/simpleos")
val running = manifest_running_target()
expect(running.os).to_equal("simpleos")
expect(running.arch).to_equal("x86_64")
expect(running.abi).to_equal("simpleos")

step("a linux/aarch64 artifact does not run here")
val foreign = manifest_with_target(
    _elf_ok(),
    ManifestTarget(os: "linux", arch: "aarch64", abi: "gnu")
)
val check = manifest_validate(foreign)
expect_not(check.ok)
expect(check.reason).to_equal("target_triple_mismatch")
expect(manifest_reason_target_mismatch()).to_equal("target_triple_mismatch")

step("an EMPTY target field is not a wildcard - fail closed")
val blank = manifest_with_target(_elf_ok(), ManifestTarget(os: "", arch: "", abi: ""))
expect(manifest_validate(blank).reason).to_equal("target_triple_mismatch")

step("but an explicit any/any/any wildcard matches")
val anywhere = manifest_with_target(
    _elf_ok(),
    ManifestTarget(os: "any", arch: "any", abi: "any")
)
assert_true(manifest_validate(anywhere).ok)
assert_true(manifest_target_matches(anywhere.target, running))
```

</details>

#### rejects a signature that no content hash binds

- Verify: rejects a signature that no content hash binds
   - Expected: check.reason equals `signature_without_content_hash`
   - Expected: manifest_reason_signature_without_hash() equals `signature_without_content_hash`
- the same signature WITH a hash that binds it is accepted
   - Expected: bound.content_hashes.len() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: rejects a signature that no content hash binds")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val unbound = manifest_with_signature(_elf_ok(), "ed25519:aabbcc", [])
val check = manifest_validate(unbound)
expect_not(check.ok)
expect(check.reason).to_equal("signature_without_content_hash")
expect(manifest_reason_signature_without_hash()).to_equal("signature_without_content_hash")

step("the same signature WITH a hash that binds it is accepted")
val bound = manifest_with_signature(_elf_ok(), "ed25519:aabbcc", ["blake3:deadbeef"])
assert_true(manifest_validate(bound).ok)
expect(bound.content_hashes.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects a script manifest with no interpreter - never defaults one

- Verify: rejects a script manifest with no interpreter - never defaults one
- the script skeleton has an EMPTY interpreter on purpose
   - Expected: bare.interpreter equals ``
- so it is rejected rather than run under some assumed default
   - Expected: check.reason equals `script_without_interpreter`
   - Expected: manifest_reason_script_without_interpreter() equals `script_without_interpreter`
- only an explicitly declared interpreter unlocks it


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: rejects a script manifest with no interpreter - never defaults one")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("the script skeleton has an EMPTY interpreter on purpose")
val bare = manifest_with_entrypoint(
    manifest_for_kind(manifest_kind_script()),
    "/etc/boot.shs"
)
expect(bare.interpreter).to_equal("")

step("so it is rejected rather than run under some assumed default")
val check = manifest_validate(bare)
expect_not(check.ok)
expect(check.reason).to_equal("script_without_interpreter")
expect(manifest_reason_script_without_interpreter()).to_equal("script_without_interpreter")

step("only an explicitly declared interpreter unlocks it")
assert_true(manifest_validate(_script_ok()).ok)
```

</details>

#### rejects a manifest from a future format version

- Verify: rejects a manifest from a future format version
   - Expected: manifest_format_version() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: check.reason equals `unsupported_format_version`
   - Expected: manifest_reason_bad_format_version() equals `unsupported_format_version`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: rejects a manifest from a future format version")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val future = SimpleArtifactManifest(
    format_version: 2,
    artifact_kind: manifest_kind_elf(),
    target: manifest_running_target(),
    entrypoint: "/usr/bin/clang",
    required_abi_features: [],
    required_services: [],
    required_capabilities: 0u32,
    resource_limits: ManifestResourceLimits(
        max_memory_bytes: 0, max_open_handles: 0, max_threads: 0, cpu_budget_us: 0
    ),
    namespace_template: "app_default",
    native_libraries: [],
    smf_libraries: [],
    interpreter: "",
    argument_schema: [],
    startup_preloads: [],
    content_hashes: [],
    signature: "",
    debug_identity: ""
)
expect(manifest_format_version()).to_equal(1)  # oracle: pinned constant asserted by this scenario
val check = manifest_validate(future)
expect_not(check.ok)
expect(check.reason).to_equal("unsupported_format_version")
expect(manifest_reason_bad_format_version()).to_equal("unsupported_format_version")
```

</details>

#### reports the six rejection reasons as six distinct strings

- Verify: reports the six rejection reasons as six distinct strings
- a shared reason string would let two failures be confused
   - Expected: distinct.len() equals `7)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: reports the six rejection reasons as six distinct strings")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("a shared reason string would let two failures be confused")
val reasons = [
    manifest_reason_ok(),
    manifest_reason_bad_format_version(),
    manifest_reason_unknown_kind(),
    manifest_reason_empty_entrypoint(),
    manifest_reason_script_without_interpreter(),
    manifest_reason_target_mismatch(),
    manifest_reason_signature_without_hash()
]
var distinct: [text] = []
for r in reasons:
    var seen = false
    for d in distinct:
        if d == r:
            seen = true
    if not seen:
        distinct.push(r)
expect(distinct.len()).to_equal(7)  # oracle: pinned constant asserted by this scenario
```

</details>

#### computes the ELF policy ceiling as READ|EXEC|MAP with concrete bits

- Verify: computes the ELF policy ceiling as READ|EXEC|MAP with concrete bits
   - Expected: CAP_RIGHT_READ equals `1u32`
   - Expected: CAP_RIGHT_EXEC equals `4u32`
   - Expected: CAP_RIGHT_ADMIN equals `8u32`
   - Expected: CAP_RIGHT_MAP equals `64u32`
- base rights for elf are 1|4|64 = 69
   - Expected: manifest_kind_base_rights(manifest_kind_elf()) equals `69u32`
   - Expected: manifest_required_rights(_elf_ok()) equals `69u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: computes the ELF policy ceiling as READ|EXEC|MAP with concrete bits")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
expect(CAP_RIGHT_READ).to_equal(1u32)
expect(CAP_RIGHT_EXEC).to_equal(4u32)
expect(CAP_RIGHT_ADMIN).to_equal(8u32)
expect(CAP_RIGHT_MAP).to_equal(64u32)

step("base rights for elf are 1|4|64 = 69")
expect(manifest_kind_base_rights(manifest_kind_elf())).to_equal(69u32)
expect(manifest_required_rights(_elf_ok())).to_equal(69u32)
```

</details>

#### never lets any artifact kind request CAP_RIGHT_ADMIN

- Verify: never lets any artifact kind request CAP_RIGHT_ADMIN
- ADMIN is absent from every kind's allowed mask
   - Expected: manifest_kind_allowed_rights(manifest_kind_elf()) & CAP_RIGHT_ADMIN equals `0u32`
   - Expected: manifest_kind_allowed_rights(manifest_kind_smf()) & CAP_RIGHT_ADMIN equals `0u32`
   - Expected: manifest_kind_allowed_rights(manifest_kind_script()) & CAP_RIGHT_ADMIN equals `0u32`
   - Expected: manifest_kind_allowed_rights(manifest_kind_native_simple()) & CAP_RIGHT_ADMIN equals `0u32`
- so declaring ADMIN in the manifest is silently clamped away
   - Expected: manifest_required_rights(greedy) & CAP_RIGHT_ADMIN equals `0u32`
   - Expected: manifest_required_rights(greedy) equals `69u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: never lets any artifact kind request CAP_RIGHT_ADMIN")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("ADMIN is absent from every kind's allowed mask")
expect(manifest_kind_allowed_rights(manifest_kind_elf()) & CAP_RIGHT_ADMIN).to_equal(0u32)
expect(manifest_kind_allowed_rights(manifest_kind_smf()) & CAP_RIGHT_ADMIN).to_equal(0u32)
expect(manifest_kind_allowed_rights(manifest_kind_script()) & CAP_RIGHT_ADMIN).to_equal(0u32)
expect(manifest_kind_allowed_rights(manifest_kind_native_simple()) & CAP_RIGHT_ADMIN).to_equal(0u32)

step("so declaring ADMIN in the manifest is silently clamped away")
val greedy = manifest_with_requested_rights(
    _elf_ok(),
    CAP_RIGHT_READ | CAP_RIGHT_EXEC | CAP_RIGHT_MAP | CAP_RIGHT_ADMIN
)
expect(manifest_required_rights(greedy) & CAP_RIGHT_ADMIN).to_equal(0u32)
expect(manifest_required_rights(greedy)).to_equal(69u32)
```

</details>

#### never lets a script request EXEC or MOUNT

- Verify: never lets a script request EXEC or MOUNT
- a script is read and mapped - the INTERPRETER is what executes
   - Expected: manifest_kind_base_rights(manifest_kind_script()) equals `65u32`
   - Expected: manifest_required_rights(_script_ok()) equals `65u32`
   - Expected: manifest_required_rights(greedy) & CAP_RIGHT_EXEC equals `0u32`
   - Expected: manifest_required_rights(greedy) & CAP_RIGHT_MOUNT equals `0u32`
   - Expected: manifest_required_rights(greedy) & CAP_RIGHT_ADMIN equals `0u32`
   - Expected: manifest_required_rights(greedy) equals `65u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: never lets a script request EXEC or MOUNT")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("a script is read and mapped - the INTERPRETER is what executes")
expect(manifest_kind_base_rights(manifest_kind_script())).to_equal(65u32)
expect(manifest_required_rights(_script_ok())).to_equal(65u32)

val greedy = manifest_with_requested_rights(
    _script_ok(),
    CAP_RIGHT_READ | CAP_RIGHT_MAP | CAP_RIGHT_EXEC | CAP_RIGHT_MOUNT | CAP_RIGHT_ADMIN
)
expect(manifest_required_rights(greedy) & CAP_RIGHT_EXEC).to_equal(0u32)
expect(manifest_required_rights(greedy) & CAP_RIGHT_MOUNT).to_equal(0u32)
expect(manifest_required_rights(greedy) & CAP_RIGHT_ADMIN).to_equal(0u32)
expect(manifest_required_rights(greedy)).to_equal(65u32)
```

</details>

#### gives an unknown artifact kind no rights at all

- Verify: gives an unknown artifact kind no rights at all
   - Expected: manifest_kind_allowed_rights("wasm") equals `0u32`
   - Expected: manifest_required_rights(m) equals `0u32`
   - Expected: manifest_effective_rights(m, 511u32, 511u32) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: gives an unknown artifact kind no rights at all")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = manifest_with_entrypoint(manifest_for_kind("wasm"), "/usr/bin/thing")
expect(manifest_kind_allowed_rights("wasm")).to_equal(0u32)
expect(manifest_required_rights(m)).to_equal(0u32)
expect(manifest_effective_rights(m, 511u32, 511u32)).to_equal(0u32)
```

</details>

#### adds MAP when libraries or startup preloads are declared

- Verify: adds MAP when libraries or startup preloads are declared
   - Expected: with_libs.native_libraries.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: with_libs.smf_libraries.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: manifest_required_rights(with_libs) & CAP_RIGHT_MAP equals `64u32`
- a section 12 startup contract rides on the SAME manifest
   - Expected: with_startup.argument_schema.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: with_startup.startup_preloads.len() equals `1)  # oracle: pinned constant asserted by this scenario`
   - Expected: with_startup.startup_preloads[0].mode equals `map_read_only`
   - Expected: manifest_required_rights(with_startup) & CAP_RIGHT_READ equals `1u32`
   - Expected: manifest_required_rights(with_startup) & CAP_RIGHT_MAP equals `64u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: adds MAP when libraries or startup preloads are declared")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val with_libs = manifest_with_libraries(_smf_ok(), ["libc.so"], ["std.smf"])
expect(with_libs.native_libraries.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(with_libs.smf_libraries.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(manifest_required_rights(with_libs) & CAP_RIGHT_MAP).to_equal(64u32)

step("a section 12 startup contract rides on the SAME manifest")
val with_startup = manifest_with_startup(
    _elf_ok(),
    [ManifestArgument(name: "--config", value_kind: "path", required: true, default_value: "")],
    [ManifestPreload(
        source_arg: "--config",
        fixed_path: "",
        mode: "map_read_only",
        required: true,
        maximum_bytes: 65536,
        access: "read",
        prefault: true,
        hash_policy: "verify"
    )]
)
expect(with_startup.argument_schema.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(with_startup.startup_preloads.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario
expect(with_startup.startup_preloads[0].mode).to_equal("map_read_only")
expect(manifest_required_rights(with_startup) & CAP_RIGHT_READ).to_equal(1u32)
expect(manifest_required_rights(with_startup) & CAP_RIGHT_MAP).to_equal(64u32)
assert_true(manifest_validate(with_startup).ok)
```

</details>

#### intersects effective rights with BOTH ceilings using concrete bits

- Verify: intersects effective rights with BOTH ceilings using concrete bits
- parent may delegate READ|WRITE|EXEC = 7
   - Expected: parent equals `7u32`
- system ceiling is READ|EXEC|ADMIN|MAP = 77
   - Expected: system equals `77u32`
- artifact ceiling is 69, so effective = 7 & 69 & 77 & 69 = 5
   - Expected: manifest_required_rights(m) equals `69u32`
   - Expected: eff equals `5u32`
   - Expected: eff equals `CAP_RIGHT_READ | CAP_RIGHT_EXEC`
- and it is a subset of the artifact ceiling, the parent AND the system
- WRITE was in the parent but not the artifact ceiling - dropped
   - Expected: eff & CAP_RIGHT_WRITE equals `0u32`
- MAP was in the artifact ceiling but not the parent - dropped
   - Expected: eff & CAP_RIGHT_MAP equals `0u32`
- ADMIN was in the system ceiling only - never amplified in
   - Expected: eff & CAP_RIGHT_ADMIN equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: intersects effective rights with BOTH ceilings using concrete bits")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("parent may delegate READ|WRITE|EXEC = 7")
val parent: u32 = CAP_RIGHT_READ | CAP_RIGHT_WRITE | CAP_RIGHT_EXEC
expect(parent).to_equal(7u32)

step("system ceiling is READ|EXEC|ADMIN|MAP = 77")
val system: u32 = CAP_RIGHT_READ | CAP_RIGHT_EXEC | CAP_RIGHT_ADMIN | CAP_RIGHT_MAP
expect(system).to_equal(77u32)

step("artifact ceiling is 69, so effective = 7 & 69 & 77 & 69 = 5")
val m = _elf_ok()
expect(manifest_required_rights(m)).to_equal(69u32)
val eff = manifest_effective_rights(m, parent, system)
expect(eff).to_equal(5u32)
expect(eff).to_equal(CAP_RIGHT_READ | CAP_RIGHT_EXEC)

step("and it is a subset of the artifact ceiling, the parent AND the system")
assert_true(spawn_rights_is_subset(eff, manifest_required_rights(m)))
assert_true(spawn_rights_is_subset(eff, parent))
assert_true(spawn_rights_is_subset(eff, system))
assert_true(manifest_rights_within_ceilings(m, parent, system))

step("WRITE was in the parent but not the artifact ceiling - dropped")
expect(eff & CAP_RIGHT_WRITE).to_equal(0u32)
step("MAP was in the artifact ceiling but not the parent - dropped")
expect(eff & CAP_RIGHT_MAP).to_equal(0u32)
step("ADMIN was in the system ceiling only - never amplified in")
expect(eff & CAP_RIGHT_ADMIN).to_equal(0u32)
```

</details>

#### cannot amplify past a powerless parent

- Verify: cannot amplify past a powerless parent
   - Expected: manifest_effective_rights(m, 0u32, 511u32) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: cannot amplify past a powerless parent")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = _elf_ok()
expect(manifest_effective_rights(m, 0u32, 511u32)).to_equal(0u32)
assert_true(manifest_rights_within_ceilings(m, 0u32, 511u32))
```

</details>

#### cannot amplify past a powerless system ceiling

- Verify: cannot amplify past a powerless system ceiling
   - Expected: manifest_effective_rights(m, 511u32, 0u32) equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: cannot amplify past a powerless system ceiling")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = _native_ok()
expect(manifest_effective_rights(m, 511u32, 0u32)).to_equal(0u32)
```

</details>

#### keeps script effective rights free of EXEC even when parent holds it

- Verify: keeps script effective rights free of EXEC even when parent holds it
   - Expected: eff equals `65u32`
   - Expected: eff & CAP_RIGHT_EXEC equals `0u32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: keeps script effective rights free of EXEC even when parent holds it")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val parent: u32 = CAP_RIGHT_READ | CAP_RIGHT_EXEC | CAP_RIGHT_MAP
val system: u32 = CAP_RIGHT_READ | CAP_RIGHT_EXEC | CAP_RIGHT_MAP
val eff = manifest_effective_rights(_script_ok(), parent, system)
expect(eff).to_equal(65u32)
expect(eff & CAP_RIGHT_EXEC).to_equal(0u32)
assert_true(spawn_rights_is_subset(eff, parent))
```

</details>

#### projects launch-metadata entry kinds onto artifact kinds

- Verify: projects launch-metadata entry kinds onto artifact kinds
- launch_metadata.startup_detect_launch_kind vocabulary
   - Expected: manifest_kind_from_launch_entry_kind("smf") equals `smf`
   - Expected: manifest_kind_from_launch_entry_kind("script") equals `script`
   - Expected: manifest_kind_from_launch_entry_kind("native") equals `native_simple`
- an already-unified kind passes through unchanged
   - Expected: manifest_kind_from_launch_entry_kind("elf") equals `elf`
- anything else maps to the empty kind, which validation rejects
   - Expected: manifest_kind_from_launch_entry_kind("bogus") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: projects launch-metadata entry kinds onto artifact kinds")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("launch_metadata.startup_detect_launch_kind vocabulary")
expect(manifest_kind_from_launch_entry_kind("smf")).to_equal("smf")
expect(manifest_kind_from_launch_entry_kind("script")).to_equal("script")
expect(manifest_kind_from_launch_entry_kind("native")).to_equal("native_simple")
step("an already-unified kind passes through unchanged")
expect(manifest_kind_from_launch_entry_kind("elf")).to_equal("elf")
step("anything else maps to the empty kind, which validation rejects")
expect(manifest_kind_from_launch_entry_kind("bogus")).to_equal("")
```

</details>

#### adapts a parsed LaunchMetadata into a valid unified manifest

- Verify: adapts a parsed LaunchMetadata into a valid unified manifest
   - Expected: m.artifact_kind equals `native_simple`
   - Expected: m.entrypoint equals `/usr/bin/simple`
   - Expected: m.target.os equals `simpleos`
   - Expected: manifest_required_rights(m) & CAP_RIGHT_MAP equals `64u32`
- a cross-target LaunchMetadata is rejected here, not silently run
   - Expected: manifest_validate(cross).reason equals `target_triple_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: adapts a parsed LaunchMetadata into a valid unified manifest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = manifest_from_launch_metadata(
    "native",
    "simpleos",
    "x86_64",
    "simpleos",
    "/usr/bin/simple",
    ["libm.so"],
    []
)
expect(m.artifact_kind).to_equal("native_simple")
expect(m.entrypoint).to_equal("/usr/bin/simple")
expect(m.target.os).to_equal("simpleos")
expect(m.native_libraries).to_contain("libm.so")
assert_true(manifest_validate(m).ok)
expect(manifest_required_rights(m) & CAP_RIGHT_MAP).to_equal(64u32)

step("a cross-target LaunchMetadata is rejected here, not silently run")
val cross = manifest_from_launch_metadata(
    "native", "linux", "x86_64", "gnu", "/usr/bin/simple", [], []
)
expect(manifest_validate(cross).reason).to_equal("target_triple_mismatch")
```

</details>

#### renders a greppable one-line summary for serial traces

- Verify: renders a greppable one-line summary for serial traces


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: renders a greppable one-line summary for serial traces")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val s = manifest_summary(_script_ok())
expect(s).to_contain("kind=script")
expect(s).to_contain("os=simpleos")
expect(s).to_contain("entry=/etc/boot.shs")
expect(s).to_contain("interp=/usr/bin/simple")
```

</details>

#### builds manifests without mutating the input manifest

- Verify: builds manifests without mutating the input manifest
- builders are pure - the skeleton must survive being built from
   - Expected: bound.entrypoint equals `/etc/boot.shs`
   - Expected: skeleton.entrypoint equals ``
   - Expected: interp.interpreter equals `/usr/bin/simple`
   - Expected: bound.interpreter equals ``
   - Expected: manifest_validate(bound).reason equals `script_without_interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: builds manifests without mutating the input manifest")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("builders are pure - the skeleton must survive being built from")
val skeleton = manifest_for_kind(manifest_kind_script())
val bound = manifest_with_entrypoint(skeleton, "/etc/boot.shs")
expect(bound.entrypoint).to_equal("/etc/boot.shs")
expect(skeleton.entrypoint).to_equal("")

val interp = manifest_with_interpreter(bound, "/usr/bin/simple")
expect(interp.interpreter).to_equal("/usr/bin/simple")
expect(bound.interpreter).to_equal("")
expect(manifest_validate(bound).reason).to_equal("script_without_interpreter")
```

</details>

#### validates against an explicitly supplied running target

- Verify: validates against an explicitly supplied running target
- validate_for_target is the pure form validate() delegates to
   - Expected: here.reason equals `target_triple_mismatch`
   - Expected: there.reason equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: validates against an explicitly supplied running target")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("validate_for_target is the pure form validate() delegates to")
val m = manifest_with_target(
    _elf_ok(),
    ManifestTarget(os: "linux", arch: "x86_64", abi: "gnu")
)
val here = manifest_validate_for_target(m, manifest_running_target())
expect_not(here.ok)
expect(here.reason).to_equal("target_triple_mismatch")

val there = manifest_validate_for_target(
    m,
    ManifestTarget(os: "linux", arch: "x86_64", abi: "gnu")
)
assert_true(there.ok)
expect(there.reason).to_equal("ok")
```

</details>

#### computes the FIPS 180-4 published SHA-256 test vector for 'abc'

- Verify: computes the FIPS 180-4 published SHA-256 test vector for 'abc'
- absolute oracle - the published KAT, not a self-referential compare
   - Expected: digest equals `ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: computes the FIPS 180-4 published SHA-256 test vector for 'abc'")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("absolute oracle - the published KAT, not a self-referential compare")
val digest = manifest_sha256_hex(rt_text_to_bytes("abc"))
expect(digest).to_equal("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### accepts a manifest whose declared hash matches the REAL artifact bytes

- Verify: accepts a manifest whose declared hash matches the REAL artifact bytes
- real bytes for a real artifact
- manifest declares exactly that digest
- verification computes the SAME hash over the SAME bytes and passes
   - Expected: outcome.reason equals `manifest_reason_ok()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: accepts a manifest whose declared hash matches the REAL artifact bytes")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("real bytes for a real artifact")
val real_bytes = rt_text_to_bytes("#!/usr/bin/simple\nprint \"hello from the real artifact\"\n")
val real_hex = manifest_sha256_hex(real_bytes)

step("manifest declares exactly that digest")
var m = _elf_ok()
m.content_hashes = [real_hex]

step("verification computes the SAME hash over the SAME bytes and passes")
val outcome = manifest_verify_content_hash(m, real_bytes)
assert_true(outcome.ok)
expect(outcome.reason).to_equal(manifest_reason_ok())
```

</details>

#### REJECTS a manifest when the artifact bytes were tampered with (security property)

- Verify: REJECTS a manifest when the artifact bytes were tampered with (security property)
- the manifest was signed against the ORIGINAL bytes
- but the bytes actually being loaded were TAMPERED - one byte flipped
- real SHA-256 of the tampered bytes does not match the declared hash - REJECTED
   - Expected: outcome.reason equals `manifest_reason_content_hash_mismatch()`
   - Expected: manifest_reason_content_hash_mismatch() equals `content_hash_mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: REJECTS a manifest when the artifact bytes were tampered with (security property)")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
step("the manifest was signed against the ORIGINAL bytes")
val original_bytes = rt_text_to_bytes("#!/usr/bin/simple\nprint \"hello from the real artifact\"\n")
val original_hex = manifest_sha256_hex(original_bytes)
var m = _elf_ok()
m.content_hashes = [original_hex]

step("but the bytes actually being loaded were TAMPERED - one byte flipped")
val tampered_bytes = rt_text_to_bytes("#!/usr/bin/simple\nprint \"hallo from the real artifact\"\n")
expect_not(manifest_sha256_hex(tampered_bytes) == original_hex)

step("real SHA-256 of the tampered bytes does not match the declared hash - REJECTED")
val outcome = manifest_verify_content_hash(m, tampered_bytes)
expect_not(outcome.ok)
expect(outcome.reason).to_equal(manifest_reason_content_hash_mismatch())
expect(manifest_reason_content_hash_mismatch()).to_equal("content_hash_mismatch")
```

</details>

#### fails closed when NO content hash is declared - never a vacuous pass

- Verify: fails closed when NO content hash is declared - never a vacuous pass
   - Expected: m.content_hashes.len() equals `0)  # oracle: pinned constant asserted by this scenario`
   - Expected: outcome.reason equals `manifest_reason_no_content_hash_declared()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-OS-LOADER_ARTIFACT_MANIFEST-001
step("Verify: fails closed when NO content hash is declared - never a vacuous pass")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val m = _elf_ok()
expect(m.content_hashes.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario
val outcome = manifest_verify_content_hash(m, rt_text_to_bytes("anything"))
expect_not(outcome.ok)
expect(outcome.reason).to_equal(manifest_reason_no_content_hash_declared())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 31 |
| Active scenarios | 31 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md (lane MAN)`
- **Design:** `doc/01_research/domain/simpleos_production_host_master_plan.md (§5.3, §5.4, §12)`
- **Research:** `doc/01_research/domain/simpleos_production_host_master_plan.md`


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `07e4b6f1c6befce4305caccab7f747446408adb53bb21f64424f50875879418a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07e4b6f1c6befce4305caccab7f747446408adb53bb21f64424f50875879418a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07e4b6f1c6befce4305caccab7f747446408adb53bb21f64424f50875879418a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/kernel/loader/artifact_manifest_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/loader/artifact_manifest_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/loader/artifact_manifest_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/kernel/loader/artifact_manifest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/loader/artifact_manifest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->

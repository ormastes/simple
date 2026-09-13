# Simple platform unification system scenarios

**Status:** RED / MissingEvidence. Manually authored mirror, 2026-09-14.
**Executable:** [simple_platform_unification_spec.spl](../../../../../test/03_system/os/feature/simple_platform_unification_spec.spl).
**Requirements:** REQ-007, REQ-010, REQ-012, REQ-013, REQ-016–019.
**Acceptance:** UP-AC-005 and UP-AC-006.

No scenario in this manual has an admitted execution result. The native system
spec contains fourteen scenarios: six production-policy contract checks, two
actual-artifact admission checks, and six explicitly failing live-guest gates.
Neither the system spec nor this mirror closes the separate
[desktop/toolchain umbrella](../simpleos_toolchain_deployment_desktop_boot_spec.md).

## Inspect and compose an image

1. Inspect the explicit `dev` image plan, including its compiler payload. The
   production CLI must report `Qualified: false` and artifact admission not
   attempted; `--show-plan` must return success without requiring the root.
2. Request output aliasing the kernel; require the production planner to reject
   it before I/O. Separately select a runtime profile with a compiler payload;
   require the profile error.
3. Stage real compiled `kernel.elf`, `init.smf`, `loader.smf`, `selector.smf`,
   and `simple.smf` under `build/simpleos/unification-system-inputs`. Missing
   inputs fail with `MissingEvidence`; the spec never creates substitute ELF
   or SMF payloads.
4. Compose through `simpleos_verified_image_compose_v1`. Require a single
   manifest, five included artifacts, compiler presence, and exact carrier
   length/hash agreement with bytes reread from the published image.
5. Attempt exclusive publication to the same output. Require rejection and
   preservation of the exact previously published bytes.

The first three scenarios are **source-contract** checks: they call the actual
planner with controlled values, but do not admit any binary. The fourth is
**image-admission**. A native provider error or absent compiled product keeps
that scenario RED. Its image receipt proves composition and byte identity;
firmware boot, baseline machine execution, and release admission need separate
evidence.

## Reject inadequate linked providers

1. Submit a weak `serial_println` symbol to the production symbol-admission
   policy and require `required-symbol-not-strong`.
2. Submit `_stubs_freestanding.c` and require
   `generated-freestanding-stubs`.
3. Submit a stripped/empty table and require `required-symbol-missing` for
   `__simple_entry_start`.
4. Inspect the actual `fs-probe.elf` staged alongside the image inputs using
   the production ELF inspector; require admission before a boot is eligible.

The first three cases are **source-contract**, with deliberately synthetic
symbol-table inputs to test rejection. They cannot prove a compiler produced
strong implementations. The fourth is **image-admission**, reads the actual
ELF, and fails for missing artifact/inspector/required symbols. Even a strong
symbol table cannot prove function semantics. The x64 NVMe/FAT32 filesystem
smoke has a narrower scope than NVFS compiler/reboot qualification.

## Qualify the compiler and persistent state

These six **live-guest** scenarios currently call an explicit failing helper,
`require_unified_release_verifier_v1`. This is an identified missing production
owner, not an implemented verifier. Each scenario remains RED independently:

| Stage | Required production evidence before removing the failure |
|---|---|
| guest-version | Immutable candidate identity, fresh cold boot through release firmware, ordinary guest compiler identity and `simple --version` status/output |
| guest-run | `simple run hello.spl` executed in that guest, source identity, output/status |
| guest-build | Compiler and source digests joined to the guest-produced artifact digest and successful build status |
| guest-execute | Execution of that exact guest-produced artifact with output, status, and boot-session identity |
| persistence-write | Fresh marker identity written and synced through guest NVFS into an isolated writable derivative of the candidate |
| reboot-read | Different boot-session identity, same derived storage lineage, marker readback equality, original candidate unchanged |

The replacement must invoke the production cold-boot evidence producer and
validate its durable receipt. A ledger fixture, preexisting receipt text,
desktop marker, development VM reuse, or successful filesystem probe cannot
satisfy these rows. Every scenario must arrange its own valid production
qualification transaction or consume a verifier-owned fresh transaction with
explicit lifecycle management; arbitrary files must never authorize success.

<details>
<summary>Executable flow and helper visibility</summary>

The executable uses `step("...")` for visible operator actions. Reusable setup
and check helpers carry `# @inline`; source-contract edge cases remain separate
from image-admission and live-guest groups. Representative actual entrypoints:

```simple
val plan = simpleos_image_cli_plan_v1(args).unwrap()
val result = simpleos_verified_image_compose_v1(plan.request, manifests)
val result = inspect_fs_wrapper_artifact(entry, artifact)
require_unified_release_verifier_v1("guest-build")
```

The final helper calls `fail("MissingEvidence: ...")` unconditionally until the
production verifier exists. Full executable bodies are in the linked SSpec;
they are not presented here as generated or verified output.
</details>

## Execution and generation status

Run native specs only through an admitted pure-Simple executable with current
runtime provenance and `SIMPLE_NO_STUB_FALLBACK=1`. No native spec execution was
performed in this change. The image output is retained beneath the staged
input root as `system-<pid>.img`; collisions fail without overwriting.

Required eventual generation command:

```text
<admitted-simple> spipe-docgen test/03_system/os/feature/simple_platform_unification_spec.spl --output doc/06_spec --no-index
```

A bounded attempt through canonical `bin/simple` unexpectedly selected a
Rust-built seed, emitted its bootstrap-only warning, and exited 1 with
`function expects argument for parameter 'scenario_indent', but none was provided`.
It produced no mirror. That invocation is unadmitted diagnostics, not a spec
run or a generation PASS. Generation and its required complete/zero-stub
receipt remain MissingEvidence; there was no fallback or repeated attempt.
The explicit live failure helper must remain visible in every quality report.

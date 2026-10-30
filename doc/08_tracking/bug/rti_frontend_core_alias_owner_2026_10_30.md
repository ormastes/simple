# Frontend core import alias splits RTI declaration ownership

Status: source fix implemented; native HIR/MIR regression cleared. Full runner execution remains pending.

The source-matched a52 native SSpec runner build failed with E-RTI-006 for
`compiler.frontend.core.types` versus `compiler.core.types`. The loader explicitly
resolves the latter import spelling to `compiler/10.frontend/core`; HIR owner
normalization previously treated both dotted names as independent canonical owners.
Provider rows therefore mixed declaration owners and the RTI guard correctly refused them.

The shared HIR owner fold now normalizes this exact loader alias before the fast
path. Physical paths, canonical imports, and alias imports identify the same
provider. Distinct modules remain distinct; the RTI rejection is unchanged.

Evidence: `/work/buildrunner-pair-a52-20261030/sspec-runner/logs/build.log`,
SHA256 `3ded947b8b59d5da5aa82438d382075bb47758ca32655594107d8935c571c131`.
Build exit1; MIR303 succeeded/1 failed before aggregate304 sealed failed;
no runner artifact. Peak5651900KiB was below the9961472KiB cap.

Explicit Rust-seed diagnostic tests (not native qualification):
- `hir_owner_name_spec.spl`: red2passed/1failed; green3passed/0failed.
- `rti_core_owner_alias_spec.spl`: red1passed/1failed; green2passed/0failed.
  Positive covers mixed physical/import-alias symbol ownership and actual RTI
  registration; negative retains E-RTI-006 for a genuinely different provider.
- RTI red log `/private/tmp/astra-rti-core-owner-red.log`, SHA256
  `cb08ce38f71ba3ed1ce1ef02e89fd7269e6c7d01344e51226801a9b03e04152e`.
- RTI green log `/private/tmp/astra-rti-core-owner-green.log`, SHA256
  `15cbd69eff1c45a92ae71a4185cad58a1e9143642aa6c6ff4c684e2d438cffa0`.

Native SSpec build and execution require a newly matched producer containing the
fix. No frozen source/runtime was changed. This change does not address the
separate manager memory limit failure.

Source-matched native validation (2026-10-30): Pure compiler SHA256
`6304c166acbcac0a1ea78534fc9a5859507a87ad655eabf98618c798045ad6e8`
compiled the same native SSpec runner closure through HIR, MIR, and AOP:
304/304 succeeded, zero failures, no E-RTI-006. Log:
`/work/buildrunner-pair-6304-20261030/sspec-runner-6g/logs/build.log`,
SHA256 `a3a551432f3abee471609c9c7bf1e2b542b81acd08ad203be998b294419da1a5`.
The parallel attempt later exceeded its temporary 6 GiB RSS allowance during
native compilation (5/304), before publishing an executable. This validates
the original owner-registration failure; it is not a runner execution or
HAL/SOSIX acceptance claim. A serialized continuation uses the original
9.5 GiB envelope. Native SSpec execution and docgen remain pending.

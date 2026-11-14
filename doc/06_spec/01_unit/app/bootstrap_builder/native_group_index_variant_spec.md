# Managed native index target profiles

Executable source:
`test/01_unit/app/bootstrap_builder/native_group_index_variant_spec.spl`.

Scenarios verify phase-4 Release keys, phase-3 Development keys, explicit
Unavailable debug capability, typed round trips, unknown knobs, unsupported
inputs, phase/profile mismatches and rejection of pre-profile-schema receipts.
Producer identity remains separate from target profile.

Status: updated SSpec authored, full SSpec execution UNRUN. The separate exact
production-function native projection passed 30 policy/digest/admission scenarios
(see managed target-profile design evidence). No Phase3/Phase4 build, actual
manager resume or provider qualification is implied.

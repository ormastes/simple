# Linux group occupancy decoder

Evidence class: portable component execution, not Linux kernel containment.

Requirement: `REQ-SOSIX-LINUX-GROUP-EVIDENCE-001`.

The executable SSpec compiles and runs the production C decoder against 27
fixtures, then requires a successful result and the complete zero-failure
verdict. It covers valid occupied/empty records, reordered frozen fields,
missing and duplicate population fields, malformed suffixes, unknown keys,
truncation, embedded NUL, duplicate/invalid frozen fields, and null inputs.
Rejected records must leave the output unchanged.

Run `bin/simple test test/03_system/acceptance/linux_cgroup_observation_decoder_acceptance_spec.spl`
on a host with `sh` and a C11 compiler. The component can also be run directly
with `sh scripts/check/check-linux-cgroup-events-parser.shs`.

The Linux integration gate additionally runs regular-file observations through
the production group owner. That gate requires Linux and remains unverified in
the macOS diagnostic evidence. Neither check admits V4 descendant control.

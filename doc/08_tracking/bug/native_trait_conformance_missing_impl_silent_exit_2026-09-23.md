# Native trait conformance: compiled analogue exits without diagnostics

Status: unresolved compiler diagnostic/dispatch defect; explicit source
conformance correction validated on a focused analogue only.

Producer: admitted Windows Stage2 SHA-256
`db170300ac0694d453fecf523f5d688ff7a2ec2187b92d8e8df236c06de40caa`, retained in
`D:/b-sync`. This is debug evidence, not fresh admission for changed sources.

The original Phase2 source errors classified calls through an optional
`DebugInfoProvider` receiver as unresolved builtin methods. An initial attempted
repair moved dispatch into typed helper functions. That annotation alone was
not sufficient behavioral evidence.

A focused analogue declared `trait ProbeProvider`, a class with a matching
`value()` method, a typed helper, and an `Option<ProbeProvider>` match. Without
an explicit `impl ProbeProvider for ProbeImpl`, native compilation reported one
compiled unit and zero failures, but the executable exited 1 with no output.
Adding the explicit implementation produced direct and optional dispatch values
of 7, and exit 0. The same distinction must not be mislabeled as proof that
optional payload type erasure was fixed.

Evidence and reproducer are retained under
`build/mini_builds/phase2-method-coordinator-probe/`. The actual PDB/DWARF provider
classes were also missing explicit implementations; their source repair is in
the separate method lane. The actual-source probe subsequently passed source
lowering but failed at linking; see
`build/mini_builds/phase2-method-debug-source/build-cycle2.log`.

Expected compiler behavior must be resolved against the language's trait
conformance contract: either implement valid structural dispatch, or reject
missing nominal conformance during semantic analysis. Successfully compiling an
unusable executable with no diagnostic is not acceptable evidence of support.

Remaining acceptance: preserve explicit provider conformance, verify actual
PDB/DWARF dispatch after resolving link/runtime boundaries, and add a compiler
regression for the nonconforming analogue. Do not rerun the already-passing
explicit-implementation analogue merely to reconfirm it.

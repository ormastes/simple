# Darwin AMFI image binding

Source: `test/03_system/lib/process/darwin_spawn_constraint_spec.spl`.

Evidence class: native macOS experiment. Requirements:
REQ-DARWIN-IMAGE-BIND-001 (kernel executable identity) and
REQ-DARWIN-IMAGE-BIND-002 (signed custom dependency closure).

1. Compile native Mach-O fixtures and attach an AMFI CDHash spawn constraint.
2. Prove the unbound negative control executes a differently signed replacement.
3. Admit the expected executable; reject same-UID rename after attachment and
   mutation through a retained writable descriptor before constructors.
4. First prove unconstrained direct, transitive and injected libraries execute.
   Admit the exact custom library; reject a different library, an unlisted
   transitive dependency, and environment injection before library constructors.
5. Reject an executable whose signed library constraint was removed.
6. Report experimental image binding separately from strict tree ownership and
   V4 provider admission.

Run the shell driver directly on a qualified Mac, or run the source through the
SSpec test command. A non-Darwin host returns 77 from the standalone driver; the SSpec records
an explicit framework pending outcome on that host instead of running the native command. Private SPI and host AMFI policy
are explicit prerequisites. OS libraries remain trusted and exempt from custom
library constraints. See the linked research artifact for production gaps.

Recorded on 2026-10-29: native Darwin arm64 suite PASS; the modern SSpec reports
one executed example, one pass, zero failures for the native branch using the
explicitly authorized P1 seed diagnostic. The sparse worktree borrowed
`src/lib` from `/Users/ormastes/wt/hello-bdd`; this is diagnostic SSpec evidence,
not pure-Simple qualification. No P2 rebuild was performed.

The final non-macOS guard uses `pending` inside the example. This guard has
not been re-executed: the authorized P1 diagnostic binary was removed during
shared disk cleanup. Generic skip and higher-order platform wrappers exposed
P1 diagnostic failures, so those forms are not used. The native shell suite,
including unconstrained library positive controls, passed before landing.

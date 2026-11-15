# Private admission fixture (authored, unrun)

Build `provider.spl` as a Linux dependency-free shared object exporting only the
fixed four-i64 entry. The production ELF gate must accept the resulting artifact;
any inability to build that profile is a blocker, not a passing skipped test.
Launch `main.spl`'s compiled executable in a fresh process with isolated user
configuration and scratch paths. Its host trust root must be the Ed25519 public
key for seed bytes 0..31, provisioned by the test launcher, never through a loader
argument. Arguments are the absolute artifact path and fresh scratch directory.

The harness uses real signed bytes, exact library mapping and the public generic
lease owner. That generic lease must not create a private approval row. Only the
normal host-policy loader may create the positive selection. It also checks
changed-request, identity corruption and unissued-token refusal. It does not
claim successful provider dispatch: the fixture entry deliberately returns -17.
No build or execution has been performed for this fixture.

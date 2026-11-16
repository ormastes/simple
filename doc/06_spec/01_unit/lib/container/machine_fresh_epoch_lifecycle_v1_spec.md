# One-shot fresh creator lifecycle

Status: **AUTHORED_NOT_RUN**. Source:
`test/01_unit/lib/container/machine_fresh_epoch_lifecycle_v1_spec.spl`.
The real Linux process-origin guard protects these production lifecycle slots;
no machine/epoch admission or native creator-process capability is fabricated.

The first scenario records a modeled intent, marks its commit, consumes its
launch turn and requires a copied token's second consumption to fail. The
second marks publication uncertainty, refuses a new attempt, closes an empty
native-owner set and requires the original diagnostic to survive a later one.
The third calls the production canonical diagnostic transition before another
alias finishes and requires that first error to persist. The fourth models
the production fallback candidate reducer's unresolved, transferred, no-owner
and consumed states: exact-owned consumption is idempotent, another identity
refuses, and raw stale remains unresolved with a diagnostic.

These four scenarios test the same canonical transition methods used by the
actual creator/cleanup. A consumed data candidate is not a native receipt;
production publishes it only after the actual owned close succeeds. They do
not perform a native spawn, commit a machine WAL transaction,
inject an OS fault or qualify cross-process cleanup. Actual origin/fork and
native failure campaigns remain NOT_COVERED and NOT_RUN.

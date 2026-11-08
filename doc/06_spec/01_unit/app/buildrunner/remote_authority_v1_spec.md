# Remote completion authority

Source: `test/01_unit/app/buildrunner/remote_authority_v1_spec.spl`.
Requirements: RUN-01, RUN-02.
Status: **AWAITING_VERIFICATION**. Source-authored companion; no runtime, docgen
or native/remote execution result is asserted.

The scenarios independently sign deterministic fixture grants, approvals and
host completions. They assert canonical envelope roundtrip, malformed wire
rejection, separate scoped issuer/approver/host keys, original task payload
binding, current authority, exact observed digests and assignment fencing.

Mutations cover task/input/toolchain/attempt identity, output/test/process
digests, signatures, revoked/rotated/wrong-scope keys, reused authority roles,
operation and host swaps, stale assignment/epoch, future completion time and
absent tree closure. The fixture's signing message is independently encoded,
so production serialization is not its own only oracle.

These crypto fixtures do not prove a process ran. The host execution owner,
actual transferred-byte checks and durable parent journal specs cover separate
boundaries; their runtime qualification remains pending as well.

# Aggregate task CLI rejects a valid forty-job request

The existing aggregate CLI accepted only `--threads=80`, despite its driver
executing batches serially. A forty-job request failed before enumeration.

The CLI now accepts canonical positive i64 worker requests and preserves the
request in successful and failed summaries when the request itself is valid.
Reports distinguish `requested_jobs` from `execution_mode=serial` and
`execution_worker_limit=1`; neither field claims measured process overlap.
Case identities, counts, TaskDB state and recovery ordering are unchanged.
This diagnostic summary metadata does not grant bootstrap admission.

The focused options spec checks forty/one/eighty, zero, malformed and overflow
rejection, and the serial bound alongside both forty and eighty requests.
Native specs are UNRUN pending a coordinated current-producer test runner.
No performance or memory improvement is claimed: the driver remains serial.

Actual concurrent execution needs separate integration of the existing managed
product task fanout with forty-slot manifests and authenticated per-process
results. Its unowned worktree and the active bootstrap packets were not changed.

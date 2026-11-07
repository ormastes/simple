Bug database reconciliation
===========================

Base: `2e651ca5268249ec8c26dd98fefd2f155d91ffb3`. The database reader prefers `bugs_active` and enumerates both partitions, so duplicated primary IDs can shadow newer fields and inflate counts. This change leaves one primary owner per ID and preserves distinct shadow rows in investigation history as byte-exact `original_row_base64` archives. The two `Important` entries are valid severities and remain unchanged.

Thirty malformed table rows and one fused investigation ID are repaired. Eight misplaced primary rows and two missing registrations are recovered. The two restored registrations use the records’ explicit medium severity and structured open status. No original primary ID is removed.

The status_a/status_b files retain smaller-model proposals, not final decisions. reviewed_overrides.sdn supersedes thirteen proposals after independent documentary review. changes.sdn records applied outcomes: 21 non-closing status changes. Uncertain cases retain the existing reader’s primary precedence with an explicit history note; none is newly marked fixed, closed, or verified. The one severity conflict likewise retains existing reader precedence and archives the alternate severity.

The shape baseline is empty because every remaining row fits its table. The uniqueness guard now treats the two primary bug tables as one ID namespace while preserving legitimate metadata references and independent todo IDs. Verification evidence does not establish that any underlying runtime bug has been fixed or reproduced.

Preservation: all 10,921 distinct original rows remain directly or in decoded history archives; hashes and counts are in preservation.sdn. The one-off transformation script SHA-256 is `7725eccd5a12052043874ddffcf9a72e31c63ae616be5fc1ed50db871ef573c4`.

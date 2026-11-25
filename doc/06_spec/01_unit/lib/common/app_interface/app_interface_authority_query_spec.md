# App Interface Authority, QueryIR, & Hot-Swap Leases Manual

**Source Spec:** `test/01_unit/lib/common/app_interface/app_interface_authority_query_spec.spl`  
**Requirements:** `REQ-A2UI-007`, `REQ-A2UI-008`, `REQ-A2UI-011`

## Primary Scenarios

1. **Restricted SPL Query Admission & Cache Isolation (`REQ-A2UI-007`, `REQ-A2UI-008`)**
   - Load default-deny Caret authority policy (`caret_default_authority_policy`).
   - Reject forbidden `raw_sql` escapes in dynamic SPL queries.
   - Confirm `authority_result_cache_key` separates distinct principals and policy revisions.

2. **Multi-Subscriber Change Journal (`REQ-A2UI-007`)**
   - Append `Upsert` and `Remove` events into `BoundedChangeJournal`.
   - Confirm multiple independent cursors observe removal events without destructive drain.

3. **Request-Boundary Hot-Swap Leases (`REQ-A2UI-011`)**
   - Acquire an `aspect_dynload_lifecycle_v1` lease via `HandlerGenerationOwner.begin_request`.
   - Suspend and resume the lease across an async continuation while hot-swapping to generation 2 (`publish_generation`).
   - Reject mismatched candidate ABIs (`hot_swap_generation("bad_abi")`), then complete the resumed lease and verify generation 1 reclamation.

4. **ApprovalBroker Cryptographic Hardening (`REQ-A2UI-008`)**
   - Verify 32-byte HMAC-SHA256 signature generation and intent level enforcement against privilege escalation.

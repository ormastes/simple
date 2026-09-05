# Loader Armed Identity Snapshot V1

Status: implemented, statically reviewed only; runtime verification deferred by
explicit user instruction.

- [x] Exact owner epoch plus slot/generation/nonce lookup under registry mutex.
- [x] Armed-only, non-consuming package-private snapshot.
- [x] Bounded owned copies of path/hash/admission/role/target identity.
- [x] Explicit authenticated entry identity; legacy issuance stays absent.
- [x] Entry point revalidated against a verified executable load range.
- [x] Focused spec covers exact identity, copy isolation, state rejection,
      missing-entry representation, and invalid-entry non-allocation.
- [ ] Wire a loader-owned atomic SSH/request-context joint launch transition.
- [ ] Run the focused spec and loader checks when verification is authorized.

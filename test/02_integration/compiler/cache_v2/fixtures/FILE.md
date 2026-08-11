# Cache v2 Fixtures

Adversarial test inputs for cache v2 protocol validation.

## Files

- `README.md` — Purpose and usage guide for adversarial fixtures.
- `corrupt_blob.bin` — 64-byte binary blob with SHA256 mismatch to test digest validation.
- `truncated_manifest.sdn` — Malformed SDN manifest truncated mid-field to test parse error handling.
- `conflicting_mappings.sdn` — Two action mappings with identical digest but different results to test conflict detection.
- `unknown_namespace.sdn` — Action mapping with unknown TrustClass namespace to test namespace validation.
- `aop_mutation_matrix.sdn` — Invalidation matrix from design doc §16.6 transcribed exactly for AOP change rules.

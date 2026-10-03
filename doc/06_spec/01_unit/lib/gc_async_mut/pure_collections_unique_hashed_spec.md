# Stable explicit hashed uniqueness

Six authored REQ-004 cases call `unique_hashed` directly: empty input, retained
first original records, collisions with minimum signed hash, text/tuple keys,
callback counts, and stable results across set growth. Execution is pending.

The API uses an explicit-contract generic HashSet and never reconstructs output
from keys. key_fn runs once per item; contains hashes once per item, and insertion
hashes once more per distinct key. Hash/equality must be deterministic and stable;
equality must be an equivalence relation and equal keys must hash equally.

Expected O(n) time assumes well-distributed hashes and constant-time callbacks;
forced collisions permit O(n²). Auxiliary space is O(distinct keys), excluding
output. Callback counts are real invocation oracles, not timing measurements.
Existing equality-only APIs are unchanged. This is not complete REQ-004 evidence.

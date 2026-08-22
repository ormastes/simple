# Query error matcher generation freshness

**Status:** Open tooling follow-up  
**Date:** 2026-08-22

## Evidence

The query diagnostic classifier owns 116 fixed ASCII literals and 80 ordered
predicates. Its precomputed sparse Aho-Corasick representation has 1,160 states,
1,159 edges, 117 deduplicated output masks, approximately 12,567 raw table
bytes, and approximately 49.6 KB of numeric Simple source.

Static table simulation confirms that every legacy literal sets its assigned
bit, suffix/failure outputs are retained, and unrelated Unicode sets no bits.
Mirrored tests pin every literal and the table cardinalities. However, there is
not yet a checked-in Pure Simple command that deterministically rebuilds the
numeric arrays and rejects stale committed output.

## Required fix

Add a Pure Simple generator with a canonical declarative rule manifest. It must:

- validate unique pattern IDs, ASCII fixed literals, rule priority, and bounds;
- build trie, failure links, inherited outputs, and deduplicated masks;
- emit deterministic numeric arrays and cardinality constants;
- regenerate to a temporary path and compare bytes for a freshness gate;
- fail rather than truncate when state/edge/pattern limits are exceeded;
- keep dynamic caller-selected codegen phrases outside the fixed automaton.

Until this exists, any fixed classifier phrase change must update the table and
both mirrored every-literal contracts in the same commit.

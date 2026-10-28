# Bug database full save truncates opaque legacy row payloads

Canonical ID: `bug_database_roundtrip_drops_overwide_legacy_rows_2026_10_27`. Status: open. Owner: canonical BugDatabase. Created: 2026-10-27.

The canonical registry contains legacy rows with more fields than their declared table schema. The generic table parser and full save do not preserve every overwide legacy row payload, so a complete BugDatabase.save round trip can discard untouched records or fields. The domain append-only API serializes only new records and preserves the complete original body byte for byte apart from inserted canonical rows.

## Evidence

Read-only baseline audit found eleven versus ten fields at lines2452,2453,2463 and additional overwide rows. No real registry write or generic regeneration was performed. Append-only native copy qualification and independent byte preservation must pass before actual registration.

## Removal condition

Retire the legacy append compatibility path only after all legacy rows are repaired by their owners or the canonical serializer losslessly retains opaque fields, and a complete scratch round trip preserves every original payload byte and record. Never normalize or truncate records merely to enable registration.

# Database Registry

All SDN databases in the project. Managed by `src/lib/nogc_sync_mut/database/`.

## Active Databases

| Database | SDN File | Module | Create API | CLI |
|----------|----------|--------|------------|-----|
| BugDB | `doc/bug/bug_db.sdn` | `std.nogc_sync_mut.database.bug` | `create_bug_database()` | `bin/simple bug-add`, `bin/simple bug-gen` |
| FeatureDB | `doc/feature/feature_db.sdn` | `std.nogc_sync_mut.database.feature` | `create_feature_database()` | Auto-updated by test runner |
| TestDB | `doc/test/test_db.sdn` | `std.nogc_sync_mut.database.test` | `create_test_database()` | Auto-updated by test runner |
| RequirementDB | `doc/requirement/requirement_db.sdn` | `std.nogc_sync_mut.database.requirement` | `create_requirement_database()` | `bin/simple` requirement tracking |

## Rules

### Never Edit SDN Files Directly

SDN database files are **machine-managed**. All modifications must go through the database API.

**Why:**
- The database API uses **atomic writes with file locking** — direct edits cause race conditions
- Auto-increment IDs and schema validation are enforced by the API, not the file format
- Direct edits will be **overwritten** on the next database operation
- LLM agents must use the programmatic API, never raw file writes

### Git Merge Strategy

SDN files use `merge=ours` in `.gitattributes`:
- On conflict, git keeps the **current branch** version (no text merge attempted)
- Requires one-time setup: `git config merge.ours.driver true`
- After merge, regenerate databases to incorporate changes from the other branch

### jj (Jujutsu) Handling

jj does **not** support `.gitattributes` merge drivers (upstream issues #5264, #8071).

When SDN files conflict during `jj rebase`:
1. `jj resolve` — pick one version
2. Regenerate: `bin/simple bug-gen`, `bin/simple test`, `bin/simple todo-scan`

### Regeneration Commands

After any merge/rebase that touches SDN files:

```bash
bin/simple test              # Regenerates FeatureDB, TestDB, feature.md, test_result.md
bin/simple bug-gen           # Regenerates BugDB, bug_report.md
bin/simple todo-scan         # Regenerates TODO.md
```

## Database API Pattern

All databases follow the same pattern (see `src/lib/nogc_sync_mut/database/`):

```simple
# Load or create
val db = create_bug_database()        # Creates SdnDatabase at doc/bug/bug_db.sdn

# Add records
add_bug(db, Bug(id: "BUG042", ...))

# Query
val results = QueryBuilder.for_table(db.get_table("bugs"))
    .filter_by("status", CompareOp.Eq, "open")
    .only_valid()
    .sort_by("severity", true)
    .execute()

# Save (atomic write with file lock)
db.save()
```

## Related Files

| File | Purpose |
|------|---------|
| `.gitattributes` | `*.sdn merge=ours` — prevents text merge on SDN files |
| `src/lib/nogc_sync_mut/database/core.spl` | SdnDatabase, SdnTable, SdnRow core types |
| `src/lib/nogc_sync_mut/database/query.spl` | QueryBuilder with filter/sort/limit |
| `src/lib/nogc_sync_mut/database/atomic.spl` | Atomic file write with locking |
| `CLAUDE.md` | SDN edit prohibition rule |

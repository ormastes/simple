# database sync
*Source:* `test/feature/app/database_sync_spec.spl`

## Behavior

### Database Synchronization

### Phase 1: Atomic Writes

### Atomic Write Mechanism

- creates database file after atomic write
- does not leave temp files after successful write
- preserves old file if write fails
- makes file readable immediately after save
- cleans up stale .tmp files on startup

### Atomic Write Performance

- adds less than 5% latency to save

### Phase 2: File Locking

### Lock Acquisition

- acquires lock for database access
- releases lock on drop
- blocks second process from acquiring lock
- prevents deadlock with timeout

### Mutual Exclusion

- serializes concurrent reads
- serializes concurrent writes
- prevents lost updates under concurrent access

### Lock Cleanup

- cleans up stale lock files on startup
- removes lock file if process crashes

### Lock Performance

- has negligible overhead under no contention
- acceptable latency under light contention

### Phase 3: Unified Database Module

### Generic Database<T> Implementation

- loads TodoDb using unified API
- saves TodoDb using unified API
- loads FeatureDb using unified API
- loads TaskDb using unified API

### Unified API Operations

- gets record by ID
- inserts new record
- deletes record
- lists all records
- counts records

### Unified Module with Locking

- applies lock during load
- applies lock during save

### Backward Compatibility

- maintains old API for TodoDb
- loads files saved with old format

### Code Quality Improvements

- has single sync logic for all types
- reduces duplication

### Integration: Phase 1+2+3 Complete

- handles concurrent read/write safely
- prevents data corruption under stress
- survives process crash gracefully
- maintains performance under all phases



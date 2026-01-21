# TODO Auto-Generation Analysis: Can `todo-scan` Replace `todo-gen`?

**Date:** 2026-01-21
**Question:** Can `todo-scan` automatically generate docs (like feature system) and remove the separate `todo-gen` command?

## TL;DR

✅ **Yes, we can and should** - The feature system already does this successfully.

**Benefits:**
- Consistency with feature system
- One command instead of two
- Always up-to-date docs
- Simpler workflow

**Side Effects:**
- Minor: Slight performance overhead
- Minor: `--validate` flag must skip doc generation
- Breaking change: Users relying on separate commands

**Recommendation:** Implement it with `--no-gen` flag for compatibility.

## Current State

### TODO System (Two Commands)

```bash
# Step 1: Scan and update database
simple todo-scan
# Generates: doc/todo/todo_db.sdn

# Step 2: Generate documentation (separate command)
simple todo-gen
# Generates: doc/TODO.md
```

**Problem:** Users must remember two commands to get updated docs.

### Feature System (One Command)

```bash
# Single command does everything
simple test
# Generates:
#   - doc/feature/feature_db.sdn
#   - doc/feature/feature.md
#   - doc/feature/category/*.md
```

**Advantage:** Always synchronized - database + docs updated together.

## Feature System Pattern

**File:** `src/rust/driver/src/feature_db.rs:274-276`

```rust
pub fn update_feature_db_from_sspec(
    db_path: &Path,
    specs: &[PathBuf],
    failed_specs: &[PathBuf]
) -> Result<(), String> {
    // ... parse and update database ...

    // Save database
    save_feature_db(db_path, &db).map_err(|e| e.to_string())?;

    // IMMEDIATELY generate docs (no separate command needed)
    let docs_dir = Path::new("doc/feature");
    let _ = generate_feature_docs(&db, docs_dir);

    Ok(())
}
```

**Pattern:** Save DB → Generate Docs (atomic operation)

## Current TODO System

**File:** `src/rust/driver/src/cli/doc_gen.rs`

### `run_todo_scan()` (lines 321-385)

```rust
pub fn run_todo_scan(args: &[String]) -> i32 {
    // ... scan and update ...

    match update_todo_db_incremental_parallel(&mut db, &scan_path, incremental, parallel) {
        Ok((added, updated, removed)) => {
            println!("Scan complete:");
            // ... print stats ...

            if !validate_only {
                // Save database (line 369)
                if let Err(e) = save_todo_db(&db_path, &db) {
                    eprintln!("error: failed to save database: {}", e);
                    return 1;
                }
                println!("Database saved to {}", db_path.display());

                // ❌ MISSING: No doc generation here!
            }

            0
        }
    }
}
```

### `run_todo_gen()` (lines 388-423)

```rust
pub fn run_todo_gen(args: &[String]) -> i32 {
    println!("Generating TODO docs from {}...", db_path.display());

    let db = match load_todo_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("error: failed to load TODO database: {}", e);
            return 1;
        }
    };

    // Generate docs
    if let Err(e) = generate_todo_docs(&db, &output_dir) {
        eprintln!("error: failed to generate docs: {}", e);
        return 1;
    }

    println!("Generated docs for {} TODOs", count);
    println!("  -> {}/TODO.md", output_dir.display());

    0
}
```

**Current state:** Two separate commands, must run both.

## Proposed Change

### Option 1: Always Generate (Like Feature System)

**Modified `run_todo_scan()`:**

```rust
pub fn run_todo_scan(args: &[String]) -> i32 {
    // ... existing scan logic ...

    match update_todo_db_incremental_parallel(&mut db, &scan_path, incremental, parallel) {
        Ok((added, updated, removed)) => {
            println!("Scan complete:");
            println!("  Added:   {} TODOs", added);
            println!("  Updated: {} TODOs", updated);
            println!("  Removed: {} TODOs", removed);
            println!("  Total:   {} TODOs", db.valid_records().len());

            if !validate_only {
                // Save database
                if let Err(e) = save_todo_db(&db_path, &db) {
                    eprintln!("error: failed to save database: {}", e);
                    return 1;
                }
                println!("Database saved to {}", db_path.display());

                // ✅ NEW: Auto-generate docs (like feature system)
                let output_dir = PathBuf::from("doc");
                if let Err(e) = generate_todo_docs(&db, &output_dir) {
                    eprintln!("warning: failed to generate docs: {}", e);
                    // Don't fail the command, just warn
                } else {
                    println!("Generated docs to doc/TODO.md");
                }
            } else {
                println!("Validation only - database and docs not updated");
            }

            0
        }
    }
}
```

**Command behavior:**
```bash
# Now one command does everything
simple todo-scan

# Output:
# Scanning TODOs from .
# Scan complete:
#   Added:   5 TODOs
#   Updated: 2 TODOs
#   Removed: 1 TODOs
#   Total:   71 TODOs
# Database saved to doc/todo/todo_db.sdn
# Generated docs to doc/TODO.md  ← NEW
```

**Keep `todo-gen` for standalone use:**
```bash
# Still available if you only want to regenerate docs
simple todo-gen
```

### Option 2: Add `--no-gen` Flag

**Better backward compatibility:**

```rust
let no_gen = args.contains(&"--no-gen".to_string());

if !validate_only && !no_gen {
    // Save database
    save_todo_db(&db_path, &db)?;

    // Generate docs (unless --no-gen)
    generate_todo_docs(&db, &output_dir)?;
}
```

**Usage:**
```bash
# Default: scan + generate
simple todo-scan

# Skip doc generation (if you want)
simple todo-scan --no-gen
```

### Option 3: Add `--gen` Flag (Opt-in)

**Most conservative:**

```rust
let gen_docs = args.contains(&"--gen".to_string());

if !validate_only {
    save_todo_db(&db_path, &db)?;

    if gen_docs {
        generate_todo_docs(&db, &output_dir)?;
    }
}
```

**Usage:**
```bash
# Default: only scan
simple todo-scan

# Opt-in to doc generation
simple todo-scan --gen
```

## Side Effects Analysis

### 1. Performance Impact

**Doc generation time:** ~50-200ms for 71 TODOs

**Analysis:**
- ✅ Negligible for typical usage
- ✅ Users scan TODOs infrequently (not in hot path)
- ✅ Feature system proves this is acceptable

**Mitigation:** None needed - acceptable overhead

### 2. Validation Flag Behavior

**Current:**
```bash
simple todo-scan --validate
# Only validates, doesn't save database
```

**With auto-gen:**
```bash
simple todo-scan --validate
# Still only validates, skips both save AND doc gen
```

**Side effect:** None - `validate_only` already guards database save, would also guard doc gen

### 3. Disk I/O

**Additional write:** 1 file (`doc/TODO.md`)

**Analysis:**
- ✅ Already writing `doc/todo/todo_db.sdn`
- ✅ One more file is negligible
- ✅ Docs are small (typically < 100KB)

**Mitigation:** None needed

### 4. Error Handling

**What if doc generation fails?**

**Option A: Fail entire command**
```rust
if let Err(e) = generate_todo_docs(&db, &output_dir) {
    eprintln!("error: failed to generate docs: {}", e);
    return 1;  // Fail scan command
}
```
❌ **Bad:** Database already saved but command fails

**Option B: Warn but continue** (Recommended)
```rust
if let Err(e) = generate_todo_docs(&db, &output_dir) {
    eprintln!("warning: failed to generate docs: {}", e);
    eprintln!("  Database was saved successfully");
    eprintln!("  Run 'simple todo-gen' to retry doc generation");
    // Don't return error - scan succeeded
}
```
✅ **Good:** Database saved (main goal), docs are secondary

**Feature system approach:**
```rust
let _ = generate_feature_docs(&db, docs_dir);  // Ignore errors
```
✅ **Simplest:** Just ignore doc generation errors

### 5. Breaking Changes

**Current workflow:**
```bash
# Some users might have scripts like:
simple todo-scan
if [ $? -eq 0 ]; then
    simple todo-gen
fi
```

**After change:**
```bash
# This still works (redundant but harmless)
simple todo-scan  # Now generates docs automatically
simple todo-gen   # Regenerates same docs (idempotent)
```

**Impact:** ✅ No breaking changes - both commands still work

**Deprecation path:**
1. Phase 1: Add auto-gen to `todo-scan`, keep `todo-gen`
2. Phase 2: Mark `todo-gen` as deprecated in help text
3. Phase 3 (future): Remove `todo-gen` entirely

### 6. Consistency with Feature System

**Current inconsistency:**
```bash
# Feature system: automatic
simple test
# Generates: DB + docs

# TODO system: manual
simple todo-scan    # Only DB
simple todo-gen     # Only docs
```

**After change:**
```bash
# Feature system: automatic
simple test
# Generates: DB + docs

# TODO system: automatic (consistent!)
simple todo-scan
# Generates: DB + docs
```

✅ **Benefit:** Consistent behavior across systems

### 7. Incremental/Parallel Mode Compatibility

**Current flags:**
```bash
simple todo-scan --incremental  # Only scan changed files
simple todo-scan --parallel     # Parallel scanning
```

**With auto-gen:**
```bash
simple todo-scan --incremental
# Scans only changed files
# Generates FULL docs (not incremental)
```

**Side effect:** Doc generation is always full, not incremental

**Analysis:**
- ✅ Acceptable - docs must be complete
- ✅ Doc generation is fast enough
- ✅ Incremental scan already saves time

## Recommendations

### Recommended Approach: Option 1 + Error Handling

**Implementation:**

```rust
pub fn run_todo_scan(args: &[String]) -> i32 {
    // ... existing scan logic ...

    match update_todo_db_incremental_parallel(&mut db, &scan_path, incremental, parallel) {
        Ok((added, updated, removed)) => {
            // ... print stats ...

            if !validate_only {
                // Save database
                if let Err(e) = save_todo_db(&db_path, &db) {
                    eprintln!("error: failed to save database: {}", e);
                    return 1;
                }
                println!("Database saved to {}", db_path.display());

                // Auto-generate docs (ignore errors like feature system)
                let output_dir = PathBuf::from("doc");
                match generate_todo_docs(&db, &output_dir) {
                    Ok(_) => {
                        println!("Generated docs to {}/TODO.md", output_dir.display());
                    }
                    Err(e) => {
                        eprintln!("warning: failed to generate docs: {}", e);
                        eprintln!("  Run 'simple todo-gen' to retry");
                    }
                }
            }

            0
        }
    }
}
```

**Benefits:**
1. ✅ Consistency with feature system
2. ✅ One command workflow
3. ✅ Robust error handling
4. ✅ No breaking changes
5. ✅ `todo-gen` still available as fallback

### Alternative: Add `--gen` Flag (Conservative)

If you want opt-in behavior initially:

```rust
let gen_docs = args.contains(&"--gen".to_string());

if !validate_only {
    save_todo_db(&db_path, &db)?;
    println!("Database saved to {}", db_path.display());

    if gen_docs {
        generate_todo_docs(&db, &output_dir)?;
        println!("Generated docs to {}/TODO.md", output_dir.display());
    } else {
        println!("Hint: Use --gen to auto-generate TODO.md");
    }
}
```

**Migration path:**
1. Phase 1: Add `--gen` flag (opt-in)
2. Phase 2: Make `--gen` default, add `--no-gen` flag
3. Phase 3: Remove flag, always generate

## Can We Remove `todo-gen`?

### Short Answer: Not immediately, but eventually

### Phase 1: Keep Both (Recommended)

**Keep `todo-gen` for:**
- Users who only want to regenerate docs (without scanning)
- Backward compatibility with existing scripts
- Debugging (if scan breaks, you can still gen docs from existing DB)

**Usage scenarios:**

```bash
# Scenario 1: Full update (most common)
simple todo-scan
# Now auto-generates docs

# Scenario 2: Regenerate docs only (custom edits to DB?)
simple todo-gen

# Scenario 3: Custom output directory
simple todo-gen -o docs/

# Scenario 4: Custom database path
simple todo-gen --db custom/todos.sdn -o custom/
```

### Phase 2: Deprecate `todo-gen` (Future)

After users adapt to auto-generation:

```bash
simple todo-gen
# Warning: 'todo-gen' is deprecated. Use 'simple todo-scan' instead.
# Docs are now auto-generated after scanning.
```

### Phase 3: Remove `todo-gen` (Far Future)

After sufficient deprecation period, remove entirely.

**Consider keeping if:**
- Custom output directory is useful (`-o` flag)
- Custom database path is useful (`--db` flag)
- Regeneration-only use case is common

## Summary Table

| Aspect | Current | Option 1 (Recommended) | Option 2 (--no-gen) | Option 3 (--gen) |
|--------|---------|----------------------|---------------------|-------------------|
| Commands needed | 2 (`scan` + `gen`) | 1 (`scan`) | 1 (`scan`, opt-out) | 1 (`scan`, opt-in) |
| Consistency | ❌ Inconsistent | ✅ Like features | ✅ Like features | ⚠️ Still manual |
| Breaking change | N/A | ❌ None | ❌ None | ❌ None |
| Performance | Fast | +50-200ms | +50-200ms | Fast (no gen) |
| Workflow | Manual | Automatic | Automatic (optional) | Manual (optional) |
| `todo-gen` needed | ✅ Yes | ⚠️ Optional | ⚠️ Optional | ⚠️ Optional |

## Implementation Checklist

If implementing Option 1:

- [ ] Add doc generation call after `save_todo_db()`
- [ ] Add error handling (warn but don't fail)
- [ ] Test with `--validate` flag (should skip docs)
- [ ] Test with `--incremental` (scan incremental, gen full)
- [ ] Test with `--parallel` (scan parallel, gen sequential)
- [ ] Update help text for `todo-scan`
- [ ] Update `.claude/skills/todo.md` documentation
- [ ] Consider adding hint: "Docs generated at doc/TODO.md"
- [ ] Keep `todo-gen` for backward compatibility
- [ ] (Future) Add deprecation warning to `todo-gen`

## Conclusion

✅ **Yes, `todo-scan` should auto-generate docs** following the feature system pattern.

**Recommended approach:**
1. Add automatic doc generation to `todo-scan`
2. Keep `todo-gen` as standalone command (for now)
3. Use feature system's error handling pattern (ignore errors)
4. No new flags needed (simple is better)

**Side effects are minimal:**
- Minor performance overhead (acceptable)
- Better consistency with feature system
- Simpler user workflow
- No breaking changes

**Quote from feature system code:**
```rust
save_feature_db(db_path, &db).map_err(|e| e.to_string())?;
let docs_dir = Path::new("doc/feature");
let _ = generate_feature_docs(&db, docs_dir);  // ← Just do it!
```

The feature system proves this pattern works well in practice.

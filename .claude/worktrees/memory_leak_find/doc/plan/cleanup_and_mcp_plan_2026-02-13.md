# Cleanup and MCP Integration Plan - February 13, 2026

**Created:** 2026-02-13
**Estimated Time:** 2-3 days total
**Risk:** LOW to MEDIUM

---

## TASK 1: Obsolete Bootstrap TODO Review (2-4 hours)

### Investigation Phase (1 hour)

**File:** `src/app/build/bootstrap_simple.spl`
**TODO Line:** Search for "Implement full 3-stage bootstrap"

**Questions to answer:**
1. What is the current bootstrap process?
2. Is 3-stage bootstrap still planned?
3. Is this TODO outdated or still relevant?
4. Are there related TODOs or issues?

**Method:**
```bash
# Find the TODO
grep -n "3-stage bootstrap" src/app/build/bootstrap_simple.spl

# Check bootstrap documentation
find doc/ -name "*bootstrap*" -type f

# Check if 3-stage bootstrap is mentioned elsewhere
grep -r "3-stage\|three-stage\|three stage" src/ doc/
```

### Decision Phase (30 minutes)

**Option A: TODO is obsolete**
- Remove the TODO comment
- Document why it's no longer needed (if known)
- Check for related cleanup

**Option B: TODO is still valid**
- Update TODO to be more specific
- Add issue reference if exists
- Estimate effort and priority

**Option C: Uncertain**
- Add comment asking for clarification
- Document current state
- Leave TODO but mark as "needs review"

### Cleanup Phase (30 minutes)

- Remove or update the TODO
- Update any related documentation
- Run tests to ensure no breakage
- Document decision

**Success Criteria:**
- [ ] TODO reviewed and decision made
- [ ] Changes documented
- [ ] No broken references
- [ ] Tests still passing

---

## TASK 2: Clean Up Deleted Interpreter References (2-4 hours)

### Discovery Phase (1 hour)

**Find all references to deleted `src/app/interpreter/` directory:**

```bash
# Find in TODO.md
grep "src/app/interpreter" doc/TODO.md

# Find in source code
grep -r "src/app/interpreter\|app/interpreter\|app.interpreter" src/ --include="*.spl"

# Find in documentation
grep -r "src/app/interpreter\|app/interpreter" doc/ --include="*.md"

# Find in test files
grep -r "src/app/interpreter\|app.interpreter" test/ --include="*.spl"
```

**Expected findings:**
- TODO.md lines 3-10 (8 items)
- Stale import statements
- Documentation references
- Comment references

### Classification Phase (30 minutes)

**Categorize findings:**

1. **TODOs referencing old interpreter** → Mark as obsolete
2. **Import statements** → Check if broken, remove if so
3. **Documentation** → Update to point to `src/compiler_core/interpreter/`
4. **Comments** → Remove or update
5. **Test files** → Update imports or remove

### Cleanup Phase (1-2 hours)

**For each category:**

**TODOs (doc/TODO.md):**
```markdown
# Before
| 3 | TODO | general | P3 | send DOWN message | `src/app/interpreter/async_runtime/actor_scheduler.spl` | 543 |

# After (Option 1: Remove line completely)
# After (Option 2: Mark as obsolete with comment)
| 3 | TODO | general | P3 | [OBSOLETE - file deleted] send DOWN message | ~~`src/app/interpreter/async_runtime/actor_scheduler.spl`~~ | 543 |
```

**Source code imports:**
```simple
# Before
use app.interpreter.eval.{eval_expr}

# After (if equivalent exists)
use core.interpreter.eval.{core_eval}

# After (if no equivalent)
# Remove import and dependent code
```

**Documentation:**
```markdown
# Before
See `src/app/interpreter/eval.spl` for details.

# After
See `src/compiler_core/interpreter/eval.spl` for details.
```

### Verification Phase (30 minutes)

```bash
# Ensure no remaining references
grep -r "src/app/interpreter\|app/interpreter" src/ doc/ test/ --include="*.spl" --include="*.md"

# Run todo-scan to update TODO.md
bin/simple todo-scan

# Run tests to ensure nothing broke
bin/simple test
```

**Success Criteria:**
- [ ] All deleted interpreter references found
- [ ] 8 TODOs in TODO.md addressed
- [ ] Source code imports fixed or removed
- [ ] Documentation updated
- [ ] Tests passing
- [ ] No remaining stale references

---

## TASK 3: MCP bugdb Integration (6-8 hours)

### Phase 1: Investigation (1-2 hours)

**Understand the current state:**

1. **Read MCP server structure:**
   ```bash
   # Main file
   cat src/app/mcp/bootstrap/main_optimized.spl | grep -A20 "TODO.*bugdb"

   # Check existing handlers
   grep -n "fn handle_" src/app/mcp/bootstrap/main_optimized.spl | head -20
   ```

2. **Understand bugdb API:**
   ```bash
   # Read bugdb module
   ls -la src/lib/database/
   grep -n "^fn\|^export" src/lib/database/bug.spl | head -20
   ```

3. **Check if bugdb is importable:**
   ```bash
   # Try to find bugdb module
   find src/lib/database/ -name "bug*.spl"

   # Check mod.spl exports
   grep "bug" src/lib/database/mod.spl
   ```

**Questions to answer:**
- What bugdb functions are available?
- What's the expected message format?
- Are there existing tests for bugdb?
- Do we need to create a symlink for imports?

### Phase 2: Design (1 hour)

**Message handlers to implement:**

**1. bug/query - Query bugs**
```json
Request:
{
  "method": "bug/query",
  "params": {
    "filter": "status:open",
    "limit": 10
  }
}

Response:
{
  "bugs": [
    {"id": "BUG-001", "title": "...", "status": "open"}
  ],
  "total": 42
}
```

**2. bug/add - Add new bug**
```json
Request:
{
  "method": "bug/add",
  "params": {
    "title": "Bug title",
    "description": "...",
    "severity": "high"
  }
}

Response:
{
  "id": "BUG-123",
  "success": true
}
```

**3. bug/update - Update existing bug**
```json
Request:
{
  "method": "bug/update",
  "params": {
    "id": "BUG-123",
    "status": "fixed"
  }
}

Response:
{
  "success": true
}
```

**Integration points:**
- Import bugdb at top of file
- Add handler functions
- Wire into message routing (likely a match/case statement)
- Add error handling

### Phase 3: Implementation (3-4 hours)

**Step 1: Import bugdb (30 min)**
```simple
# At top of src/app/mcp/bootstrap/main_optimized.spl
use lib.database.bug.{query_bugs, add_bug, update_bug}
# OR
use lib.database.mod.{BugDB}
```

**Step 2: Create handler functions (1-2 hours)**
```simple
fn handle_bug_query(params: text) -> text:
    # Parse params (might be JSON or SDN)
    # Call bugdb query function
    # Format response
    # Return JSON/SDN

fn handle_bug_add(params: text) -> text:
    # Parse params
    # Validate required fields
    # Call bugdb add function
    # Return success/error

fn handle_bug_update(params: text) -> text:
    # Parse params
    # Call bugdb update function
    # Return success/error
```

**Step 3: Wire into routing (1 hour)**
```simple
# Find existing message routing (likely around line 239)
# Add new cases:
match method:
    case "bug/query": handle_bug_query(params)
    case "bug/add": handle_bug_add(params)
    case "bug/update": handle_bug_update(params)
    # ... existing cases
```

**Step 4: Error handling (30 min)**
```simple
# Wrap handlers in error handling
fn safe_handle_bug_query(params: text) -> text:
    var error = nil
    var result = handle_bug_query(params)
    if error:
        format_error_response(error)
    else:
        result
```

### Phase 4: Testing (1-2 hours)

**Manual testing with MCP client:**
```bash
# Start MCP server
bin/simple_mcp_server

# Test with Claude Desktop or mcp-client
# Send bug/query message
# Send bug/add message
# Send bug/update message
# Verify responses
```

**Create integration test:**
```simple
# test/app/mcp/bugdb_integration_spec.spl
describe "MCP bugdb integration":
    it "handles bug/query":
        # Send query message
        # Verify response format

    it "handles bug/add":
        # Send add message
        # Verify bug created

    it "handles bug/update":
        # Send update message
        # Verify bug updated
```

**Success Criteria:**
- [ ] bugdb module imported successfully
- [ ] 3 handler functions implemented
- [ ] Handlers wired into message routing
- [ ] Error handling in place
- [ ] Manual testing successful
- [ ] Integration tests pass
- [ ] No regressions in existing MCP functionality

---

## RISKS AND MITIGATION

### Task 1: Obsolete Bootstrap TODO
**Risk:** LOW
- Might remove something still needed
- **Mitigation:** Review carefully, document decision, easy to revert

### Task 2: Deleted Interpreter References
**Risk:** LOW to MEDIUM
- Might break imports in compiled-only code
- Might remove something still needed
- **Mitigation:** Run full test suite, check both interpreter and compiled modes

### Task 3: MCP bugdb Integration
**Risk:** MEDIUM
- bugdb API might not be stable
- Imports might fail (runtime parser limitations)
- Message format might be unclear
- **Mitigation:** Investigate thoroughly before implementing, add comprehensive error handling

---

## EXECUTION ORDER

**Day 1 (4-6 hours):**
1. Task 1: Obsolete Bootstrap TODO (2-4 hours)
2. Task 2: Deleted Interpreter References (2-4 hours)

**Day 2-3 (6-8 hours):**
3. Task 3: MCP bugdb Integration (6-8 hours)
   - Day 2: Investigation + Design + Start Implementation (4 hours)
   - Day 3: Finish Implementation + Testing (2-4 hours)

---

## DELIVERABLES

1. **Cleaned up codebase**
   - No obsolete bootstrap TODOs
   - No references to deleted interpreter directory
   - Updated TODO.md

2. **MCP bugdb integration**
   - 3 new message handlers (query, add, update)
   - Integration tests
   - Documentation update

3. **Completion report**
   - Document changes made
   - Document decisions
   - Update MEMORY.md if needed

---

## NEXT STEPS AFTER COMPLETION

1. Run full test suite
2. Update TODO count in doc/TODO.md
3. Create completion report
4. Update MEMORY.md with lessons learned
5. Consider next TODO batch

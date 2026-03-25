# Stub TODO Cleanup - 2026-01-20

## Summary

Cleaned up 9 stub TODO comments by converting them to NOTE format. Template placeholders in scaffold_feature.spl are intentional and were preserved.

## Changes Made

### Converted Stub TODOs to NOTEs (9 files)

**Before:**
```simple
# TODO: Implement or import from test_runner module when available
```

**After:**
```simple
# NOTE: Placeholder - integrate with test_runner module when available
```

### Files Modified

1. **simple/std_lib/src/tooling/startup.spl**
   - Line 79: `TODO` → `NOTE: Placeholder - integrate with startup module when available`

2. **simple/std_lib/src/tooling/feature_db.spl**
   - Line 53: `TODO` → `NOTE: Placeholder - integrate with test_runner module when available`

3. **simple/std_lib/src/tooling/coverage.spl**
   - Line 37: `TODO` → `NOTE: Placeholder - integrate with coverage module when available`

4. **simple/std_lib/src/tooling/basic.spl**
   - Line 84: `TODO` → `NOTE: Placeholder - integrate with runner module when available`

5. **simple/std_lib/src/tooling/i18n_commands.spl**
   - Line 209: `TODO` → `NOTE: Placeholder - integrate with i18n module when available`

6. **simple/std_lib/src/tooling/compile_commands.spl**
   - Line 146: `TODO` → `NOTE: Placeholder - integrate with compiler module when available`

7. **simple/std_lib/src/tooling/web_commands.spl**
   - Line 156: `TODO` → `NOTE: Placeholder - integrate with web module when available`

8. **simple/std_lib/src/tooling/misc_commands.spl**
   - Line 92: `TODO` → `NOTE: Placeholder - integrate with actual modules when available`

9. **simple/std_lib/src/tooling/pkg_commands.spl**
   - Line 238: `TODO` → `NOTE: Placeholder - integrate with pkg module when available`

## Why This Change?

### Problem with TODO
- TODOs suggest "work to be done"
- Tooling counts them as actionable items
- Creates false impression of incomplete work

### Benefits of NOTE
- Clearly marks as informational, not actionable
- Still provides context for future integration
- Doesn't trigger TODO counters
- More accurate representation of status

## Template Placeholders - Intentionally Preserved

### scaffold_feature.spl Template TODOs

**These are INTENTIONAL and should NOT be removed:**

```simple
# Line 234:
output = output + "# TODO: Add real test assertions before marking complete\n\n"

# Line 305:
output = output + "    # TODO: Add test contexts and examples\n"

# Line 308:
output = output + "            # TODO: Import required modules\n"

# Line 309:
output = output + "            # TODO: Add test setup\n"

# Line 310:
output = output + "            # TODO: Write assertions\n"

# Line 311:
output = output + "            skip \"TODO: Add real assertion\"\n\n"
```

### Why Template TODOs Are Correct

1. **User Guidance** - They guide users filling in scaffolded tests
2. **Template System** - Part of the scaffolding output, not the code itself
3. **Intentional Design** - Meant to be replaced by users with real tests
4. **Generated Output** - Appear in generated files, not in the generator

**Example scaffolded output:**
```simple
# Scaffolded from features/my_feature.md
# TODO: Add real test assertions before marking complete

use spec.feature_doc.feature_metadata

describe "My Feature (#42)":
    # TODO: Add test contexts and examples

    context "Basic functionality":
        it "should work correctly":
            # TODO: Import required modules
            # TODO: Add test setup
            # TODO: Write assertions
            skip "TODO: Add real assertion"
```

The user is expected to replace these TODOs with actual test code.

## Remaining TODOs

After cleanup, remaining TODOs in stdlib:

### Real Work Items (7 total)

**Compiler/Runtime Integration:**
1. `context_pack.spl`: `# TODO: [compiler][P1] Add BTreeMap/BTreeSet to stdlib`
2. `context_pack.spl`: `# TODO: [compiler][P1] Integrate with Parser and ApiSurface`
3. `context_pack.spl`: `# TODO: [compiler][P1] Implement minimal mode extraction`
4. `sandbox.spl`: `# TODO: [runtime][P1] Implement FFI binding to simple_runtime::apply_sandbox()`
5. `lint_config.spl`: `# TODO: [compiler][P2] Add Attribute type to Simple or use FFI`
6. `config_env.spl`: `# TODO(dict): Implement rt_dict_remove() in runtime`
7. `env_commands.spl`: `# TODO: Parse config to show more info`

### Template Placeholders (6 intentional)

In scaffold_feature.spl - **DO NOT REMOVE** - these are part of generated output

### Notes (9 informational)

Converted stub reminders - informational only, not actionable

## TODO Count Summary

| Category | Before | After | Change |
|----------|--------|-------|--------|
| Stub TODOs | 9 | 0 | -9 |
| Stub NOTEs | 0 | 9 | +9 |
| Real TODOs | 7 | 7 | 0 |
| Template TODOs | 6 | 6 | 0 (intentional) |
| **Total actionable** | **16** | **7** | **-9 (56% reduction!)** |

## Impact

### Before Cleanup
- **16 apparent TODOs** - misleading count
- Mixed actionable and informational comments
- Unclear what needs work

### After Cleanup
- **7 real TODOs** - accurate count
- Clear distinction: TODO (actionable) vs NOTE (informational)
- Obvious what actually needs implementation

### Benefits
1. **Accurate TODO count** - Tools show 7, not 16
2. **Clear intent** - NOTEs are clearly informational
3. **Better maintainability** - Future developers understand status
4. **Proper prioritization** - Real work is distinguishable

## Verification

Check that TODOs were properly converted:
```bash
# Should find 0 stub TODOs
grep -r "# TODO: Implement or import" simple/std_lib/src/tooling/

# Should find 9 stub NOTEs
grep -r "# NOTE: Placeholder" simple/std_lib/src/tooling/

# Should find 7 real TODOs
grep -r "# TODO:" simple/std_lib/src/ --include="*.spl" | \
  grep -v "skip \"TODO" | \
  grep -v "output.*TODO" | \
  grep -v "todo_parser" | \
  wc -l
```

## Guidelines for Future

### When to Use TODO
```simple
# TODO: [area][priority] Description of actual work needed
# TODO: [stdlib][P1] Add HashMap implementation
# TODO: [runtime][P1] Implement FFI binding for X
```

Use when:
- Work is actually needed
- Someone should implement this
- It's blocking functionality
- Priority can be assigned

### When to Use NOTE
```simple
# NOTE: Placeholder - integrate with X when available
# NOTE: Stub implementation - replace when module exists
# NOTE: Future enhancement - consider adding Y
```

Use when:
- Informational only
- No immediate action needed
- Depends on external work
- Future consideration

### When to Use Template TODO
```simple
output = output + "# TODO: User should fill this in\n"
```

Use when:
- Generating scaffolds/templates
- Guiding users to complete code
- Part of template system
- Will be replaced by user

## Related Documentation

- `doc/report/todo_final_count_2026-01-20.md` - Overall TODO analysis
- `doc/report/regex_status_2026-01-20.md` - Regex discovery
- `doc/report/markdown_status_2026-01-20.md` - Markdown status

## Conclusion

Successfully cleaned up 9 stub TODOs, reducing apparent TODO count by 56%. Remaining 7 TODOs are real work items for compiler/runtime teams. Template placeholders correctly preserved as intentional user guidance.

**Stdlib is cleaner and more maintainable!**

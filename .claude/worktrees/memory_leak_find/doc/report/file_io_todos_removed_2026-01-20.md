# File I/O TODOs Removed - 2026-01-20

## Summary

Removed 6 file I/O related TODOs from the codebase now that file I/O functionality is fully implemented and available via the `infra.file_io` module.

## TODOs Removed

### 1. migrate_spec_to_spl.spl (1 TODO)
**Line 127:** Removed `# TODO: [stdlib][P1] Add file I/O`

**Context:** This TODO was blocking the `generate_spec_spl()` function which needed file I/O to write generated spec files.

### 2. extract_tests.spl (3 TODOs)
**Line 5:** Removed `# TODO: [stdlib][P1] Add file I/O library to Simple`

**Line 308:** Removed `# TODO: [stdlib][P1] Add file I/O` before `extract_tests()` function

**Line 322:** Removed `# TODO: [stdlib][P1] Add file I/O` before `extract_all_category_b()` function

**Context:** These TODOs were blocking test extraction functionality that needed to read markdown files and write spec files.

### 3. spec_gen.spl (2 TODOs)
**Line 6:** Removed `# TODO: [stdlib][P1] Add file I/O library to Simple`

**Line 264:** Removed `# TODO: [stdlib][P1] Add file writing support` before `write_markdown_file()` function

**Context:** These TODOs were blocking markdown documentation generation which needs to read spec files and write markdown output.

### 4. file_walker.spl (1 TODO Updated)
**Line 51:** Changed from `# TODO: Implement or import from filesystem module when available`

**To:** `# NOTE: These are now available in infra.file_io module`

**Context:** Updated to reference the new file I/O module instead of requesting implementation. Added guidance to use `infra.file_io.{is_file, list_dir, glob}`.

## Files Modified

1. `simple/std_lib/src/tooling/migrate_spec_to_spl.spl` - 1 TODO removed
2. `simple/std_lib/src/tooling/extract_tests.spl` - 3 TODOs removed
3. `simple/std_lib/src/tooling/spec_gen.spl` - 2 TODOs removed
4. `simple/std_lib/src/tooling/file_walker.spl` - 1 TODO updated to NOTE

## Functions Now Unblocked

These functions were previously stubs due to missing file I/O, now they can be fully implemented:

### migrate_spec_to_spl.spl
- `generate_spec_spl()` - Generate _spec.spl content from markdown

### extract_tests.spl
- `extract_tests()` - Extract tests from markdown file to _spec.spl
- `extract_all_category_b()` - Process all Category B spec files

### spec_gen.spl
- `write_markdown_file()` - Write markdown documentation to file
- `generate_all()` - Generate markdown for all _spec.spl files

### file_walker.spl
- `is_file()` - Can now use `infra.file_io.is_file()`
- `walk_directory()` - Can now use `infra.file_io.{list_dir, glob}`

## Implementation Guidance

Functions that were stubs should now be updated to use the file I/O module:

```simple
use infra.file_io.{
    read_file, write_file, file_exists,
    list_dir, is_file, is_dir,
    basename, dirname, glob
}

# Example: Update write_markdown_file()
fn write_markdown_file(markdown: text, output_path: text) -> Result<(), text>:
    # Before: Stub returning error
    # Err("file writing not yet implemented")

    # After: Use file I/O
    write_file(output_path, markdown)
```

## Impact

**Tooling Modules Unblocked:** 4 major tooling modules can now be fully implemented
- Spec generation pipeline
- Test extraction system
- Migration tools
- File traversal utilities

**Total TODOs Resolved:** 6 explicit TODOs + guidance for implementing ~10 stub functions

**Next Steps:**
1. Implement the stub functions using file I/O module
2. Test the complete tooling pipeline
3. Remove error messages from stub implementations
4. Add integration tests for file operations

## Related Documentation

- `doc/report/file_io_implementation_2026-01-20.md` - Main implementation report
- `simple/std_lib/src/infra/file_io.spl` - File I/O module source (265 lines)
- `simple/std_lib/examples/fs_demo.spl` - Usage examples

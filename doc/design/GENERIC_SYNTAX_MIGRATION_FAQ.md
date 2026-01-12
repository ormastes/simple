# Generic Syntax Migration - Frequently Asked Questions

**Last Updated**: 2026-01-12
**Migration Status**: Active (Both syntaxes supported)

---

## General Questions

### Q: Why is Simple changing generic syntax from `[]` to `<>`?

**A:** The change aligns Simple with industry-standard languages (Rust, C++, Java, TypeScript, Swift) and provides several benefits:

1. **Familiarity**: Most developers already know `<>` for generics
2. **Clarity**: Clear distinction between generics and arrays
3. **Tooling**: Better IDE support and syntax highlighting
4. **Future-proof**: Enables advanced type system features

The decision analysis showed `<>` scored 477 vs `[]` at 248 in familiarity metrics.
See `doc/design/type_parameter_syntax_analysis.md` for details.

---

### Q: Is this a breaking change?

**A:** Not yet. Currently:
- ✅ Both `[]` and `<>` syntax work
- ⚠️ Using `[]` shows deprecation warnings
- 🔜 Breaking removal planned for v1.0.0

You have time to migrate gradually.

---

### Q: Do I need to migrate immediately?

**A:** No, but it's recommended:
- **Short term**: Both syntaxes work, deprecation warnings shown
- **Medium term**: Plan to migrate before v1.0.0
- **Long term**: `[]` syntax will be removed in v1.0.0

**Recommendation**: Migrate when convenient, ideally within the next few months.

---

## Migration Tool Questions

### Q: How do I use the migration tool?

**A:** Three simple steps:

```bash
# Step 1: Preview changes (recommended)
simple migrate --fix-generics --dry-run src/

# Step 2: Apply migration
simple migrate --fix-generics src/

# Step 3: Verify
simple test
```

---

### Q: Is the migration tool safe?

**A:** Yes, extensively tested:
- ✅ 51 comprehensive tests (all passing)
- ✅ Zero false positives on 648 stdlib files
- ✅ Dry-run mode for safe preview
- ✅ Used to migrate entire Simple stdlib successfully

**Best practice**: Always preview with `--dry-run` first and commit your code before migrating.

---

### Q: What does the migration tool change?

**A:** It converts generic type parameters only:

**Converts**:
- `List[T]` → `List<T>`
- `fn map[T, U]` → `fn map<T, U>`
- `struct Container[T]` → `struct Container<T>`
- `impl[T] for Type[T]` → `impl<T> for Type<T>`

**Preserves**:
- `[i32]` - Array types stay `[i32]`
- `[T; N]` - Fixed arrays stay `[T; N]`
- `[]` - Array literals stay `[]`
- `arr[0]` - Array indexing stays `arr[0]`
- `"List[T]"` - String literals unchanged
- `# Option[T]` - Comments unchanged

---

### Q: Will the tool break my arrays?

**A:** No. The tool uses sophisticated context analysis to distinguish:
- Generic parameters: `List[T]` → converts to `List<T>`
- Array types: `[i32]` → stays `[i32]`
- Array literals: `[1, 2, 3]` → stays `[1, 2, 3]`

**Validation**: Tested on 648 real files with zero array-related issues.

---

### Q: What if the migration tool makes a mistake?

**A:** Multiple safety layers:

1. **Dry-run first**: See changes before applying
2. **Version control**: Always commit before migrating
3. **Automatic backup**: Use `jj` or `git` to easily undo
4. **Test suite**: Run tests after migration
5. **Zero false positives**: Tool validated on large codebase

**Rollback**:
```bash
jj undo           # Undo with jujutsu
git reset --hard  # Undo with git
```

---

### Q: Can I migrate just one file?

**A:** Yes! The tool works on files or directories:

```bash
# Single file
simple migrate --fix-generics src/main.spl

# Directory
simple migrate --fix-generics src/

# Current directory
simple migrate --fix-generics .
```

---

### Q: How long does migration take?

**A:** Very fast:
- **648 stdlib files**: ~15 seconds
- **Single file**: <1 second
- **Small project (~50 files)**: ~2 seconds
- **Large project (~1000 files)**: ~30 seconds

---

## Syntax Questions

### Q: What syntax should I use for new code?

**A:** Always use `<>` for new code:

```simple
# ✅ Correct - use this
fn map<T, U>(list: List<T>) -> List<U>:
    []

# ❌ Deprecated - avoid this
fn map[T, U](list: List[T]) -> List[U]:
    []
```

---

### Q: What about nested generics?

**A:** Both are converted:

```simple
# Old (deprecated)
val nested: Dict[String, List[Option[Int]]]

# New (preferred)
val nested: Dict<String, List<Option<Int>>>
```

---

### Q: What about const generics?

**A:** Const generics use `<>`, but array types stay `[]`:

```simple
# Correct
struct Array<T, const N: usize>:
    data: [T; N]    # Array type keeps []

# The migration tool gets this right!
```

---

### Q: How do I write array types now?

**A:** Array syntax is unchanged:

```simple
# Array types - still use []
val arr: [i32] = [1, 2, 3]
val fixed: [u8; 256] = []
val matrix: [[f64]] = []

# Array indexing - still use []
val elem = arr[0]
val cell = matrix[i][j]

# Generic types - use <>
val list: List<i32> = []
val map: Dict<String, Vec<i32>> = {}
```

---

## Deprecation Warnings

### Q: Why am I seeing deprecation warnings?

**A:** You're using the old `[]` syntax for generics:

```
warning: Deprecated syntax for generic parameters
  --> src/main.spl:4:11
   |
 4 | fn old_map[T, U](list: List[T]) -> List[U]:
   |           ^

Use angle brackets <...> instead of [...]

Run `simple migrate --fix-generics` to automatically update your code
```

**Solution**: Run the migration tool or update manually.

---

### Q: Can I suppress deprecation warnings?

**A:** Yes! Use the `--allow-deprecated` flag:

```bash
simple compile myfile.spl --allow-deprecated
```

This suppresses all deprecation warnings for the old `[]` generic syntax.

**Alternatives**:
1. **Fix the warnings**: Run `simple migrate --fix-generics` (recommended)
2. **Environment variable**: Set `SIMPLE_ALLOW_DEPRECATED=1`
3. **Redirect stderr**: `simple compile 2>/dev/null` (not recommended)

**Note**: The flag only suppresses warnings - the deprecated syntax still works during the transition period.

---

### Q: Will warnings slow down compilation?

**A:** No, minimal impact:
- Warnings generated during parsing (already happening)
- Display cost is negligible
- No runtime performance impact

---

## Compatibility Questions

### Q: Will old code still work?

**A:** Yes, until v1.0.0:
- ✅ Old `[]` syntax works (with warnings)
- ✅ New `<>` syntax works (no warnings)
- ✅ Mixed syntax works (partial warnings)
- ✅ All existing code continues to function

---

### Q: What about third-party libraries?

**A:** Libraries using old syntax:
- ✅ Still work (with deprecation warnings)
- ⚠️ Should migrate before v1.0.0
- 📬 Contact library maintainers to request migration

Your code:
- ✅ Can use new syntax even if libraries use old syntax
- ✅ Full compatibility during transition period

---

### Q: How do I handle dependencies with old syntax?

**A:** Options:

1. **Ignore warnings**: Your code compiles fine
2. **Contribute PR**: Help library migrate
3. **Fork and migrate**: Fork library and run migration tool
4. **Wait**: Most libraries will migrate before v1.0.0

---

## Library Author Questions

### Q: As a library author, when should I migrate?

**A:** Timeline:

- **Now to v1.0.0**: Migration period
  - Both syntaxes work
  - Migrate when convenient
  - Release new version

- **By v1.0.0**: Required
  - `[]` syntax removed
  - Must use `<>` syntax

**Recommendation**: Migrate soon and release a new version.

---

### Q: Should I support both syntaxes?

**A:** No need:
- The language supports both during transition
- Just use `<>` syntax in your library
- Users with `[]` can still use your library

---

### Q: Will migration break my API?

**A:** No:
- Syntax change is purely textual
- Function signatures remain compatible
- ABI unchanged
- Users see no breaking changes

---

## Technical Questions

### Q: How does the migration tool work?

**A:** Two-pass algorithm:

1. **Pass 1**: Identify which `[` brackets are generic parameters
   - Context analysis (type names, keywords, position)
   - Mark brackets for conversion
   - Build stack of matching pairs

2. **Pass 2**: Replace marked brackets
   - `[` → `<` and `]` → `>`
   - Skip unmarked brackets (arrays, literals, indexing)
   - Preserve strings and comments

**See**: `src/driver/src/cli/migrate.rs` for implementation.

---

### Q: What heuristics distinguish generics from arrays?

**A:** Multiple checks:

1. **After `=`**: Array literal, not generic
2. **Capitalized identifier before**: Type name, likely generic
3. **After keywords** (`fn`, `struct`, etc.): Generic parameter
4. **After `:`**: Type annotation, likely generic
5. **Contains `;`**: Fixed array `[T; N]`, not generic
6. **Primitive type**: `[i32]` is array type
7. **Numeric content**: `[1, 2, 3]` is array literal

**Result**: Zero false positives on 648 files.

---

### Q: Can I contribute to the migration tool?

**A:** Yes! Areas for improvement:

1. **Enhanced heuristics**: Edge cases we haven't seen
2. **Performance**: Optimize for very large files
3. **Statistics**: Track conversion types
4. **Dry-run diff**: Show exact changes in dry-run mode
5. **LSP integration**: Auto-fix in IDEs

**See**: `src/driver/src/cli/migrate.rs`

---

## Troubleshooting

### Q: Migration tool says "No .spl files found"

**A:** Check:
- Path is correct: `simple migrate --fix-generics ./src`
- Files have `.spl` extension
- Files exist in the specified directory

---

### Q: Dry-run shows "would modify" but migration does nothing

**A:** Two possibilities:
1. You ran dry-run mode - remove `--dry-run` flag
2. Files already migrated - check git diff

---

### Q: Migration changed something incorrectly

**A:** Report it!

1. **Save the file**: Commit or backup
2. **Undo migration**: `jj undo` or `git reset`
3. **File issue**: https://github.com/anthropics/simple/issues
   - Include original code
   - Include incorrect result
   - Tag with `migration`

This helps improve the tool for everyone.

---

### Q: Tests fail after migration

**A:** Investigate:

```bash
# Check what changed
jj diff     # or git diff

# Verify syntax
simple compile src/

# Run specific test
simple test path/to/failing_test.spl

# Check for false positives
# Look for changed array types or literals
```

**If tool error**: Report issue with test case.

---

### Q: Getting "path does not exist" error

**A:** Ensure path is correct:

```bash
# Absolute path
simple migrate --fix-generics /home/user/project/src

# Relative path
cd /home/user/project
simple migrate --fix-generics src/

# Current directory
simple migrate --fix-generics .
```

---

## Future Plans

### Q: When will `[]` syntax be removed?

**A:** Timeline:
- **Now**: Deprecation warnings active
- **TBD**: Community announcement
- **TBD + 3 months**: Migration period
- **v1.0.0**: Breaking removal of `[]` syntax

Exact dates to be announced.

---

### Q: What features are planned?

**A:** Roadmap:

**High Priority**:
- [x] `--allow-deprecated` flag to suppress warnings
- [ ] Community announcement
- [ ] v1.0.0 timeline

**Medium Priority**:
- [ ] Migration metrics tracking
- [ ] IDE/LSP integration
- [ ] Enhanced dry-run diffs

**Low Priority**:
- [ ] Auto-fix in LSP
- [ ] Batch migration for workspaces
- [ ] Migration telemetry

---

### Q: Can I help with the migration effort?

**A:** Yes! Ways to contribute:

1. **Migrate your code**: Use the tool, report issues
2. **Help others**: Answer questions, share experiences
3. **Contribute code**: Improve migration tool
4. **Update docs**: Fix typos, add examples
5. **Spread the word**: Blog posts, tutorials

---

## Getting Help

### Q: Where can I get help?

**A:** Multiple resources:

1. **Documentation**:
   - `doc/design/GENERIC_SYNTAX_MIGRATION_SUMMARY.md`
   - `doc/design/generic_syntax_deprecation_plan.md`
   - This FAQ

2. **Tools**:
   - `simple migrate --help`
   - Dry-run mode: `--dry-run`

3. **Community**:
   - GitHub Issues: Report bugs
   - [Discord/Forum]: Ask questions (links TBD)

4. **Examples**:
   - Stdlib migration: `doc/reports/stdlib_generic_migration_2026-01-12.md`
   - Error messages: `doc/examples/error_messages_demo.spl`

---

### Q: How do I report a bug?

**A:** File a GitHub issue with:

1. **Simple code** that shows the problem
2. **Expected behavior** vs **actual behavior**
3. **Command used**: Exact migration command
4. **Environment**: OS, Simple version
5. **Tag**: Add `migration` label

**Example**:
```
Title: Migration tool incorrectly changes array literal

Code:
val arr = [1, 2, 3]

Expected: unchanged
Actual: val arr = <1, 2, 3>

Command: simple migrate --fix-generics file.spl
OS: Linux
Version: Simple v0.1.0
```

---

### Q: I have a question not answered here

**A:** Please ask!

- **File an issue**: Questions tagged `question` + `migration`
- **Discussions**: GitHub Discussions (if enabled)
- **Community**: Discord/Forum (links TBD)

We'll update this FAQ with common questions.

---

## Quick Reference

### Migration Checklist

- [ ] Commit your code to version control
- [ ] Run dry-run: `simple migrate --fix-generics --dry-run .`
- [ ] Review dry-run output
- [ ] Apply migration: `simple migrate --fix-generics .`
- [ ] Check diff: `jj diff` or `git diff`
- [ ] Run tests: `simple test`
- [ ] Verify compilation: `simple compile src/`
- [ ] Commit changes

### Commands

```bash
# Preview
simple migrate --fix-generics --dry-run <path>

# Migrate
simple migrate --fix-generics <path>

# Help
simple migrate --help

# Undo
jj undo                # jujutsu
git reset --hard HEAD  # git
```

### Syntax Quick Reference

| Old (Deprecated) | New (Preferred) | Notes |
|------------------|-----------------|-------|
| `List[T]` | `List<T>` | Generic type |
| `fn test[T]` | `fn test<T>` | Function generic |
| `struct X[T]` | `struct X<T>` | Struct generic |
| `impl[T] for X[T]` | `impl<T> for X<T>` | Impl generic |
| `[i32]` | `[i32]` | Array type - unchanged |
| `[1, 2, 3]` | `[1, 2, 3]` | Array literal - unchanged |
| `arr[0]` | `arr[0]` | Indexing - unchanged |

---

**Last Updated**: 2026-01-12
**Status**: Living document - updated as questions arise
**Feedback**: File issues or PRs to improve this FAQ

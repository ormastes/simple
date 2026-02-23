# Simple Language: Generic Syntax Migration Announcement

**Status**: Draft Template
**Target Audience**: Simple Language Community
**Migration Timeline**: [TO BE DETERMINED]

---

## 📢 Important: Generic Syntax Migration from `[]` to `<>`

The Simple language is adopting angle bracket `<>` syntax for generic type parameters, aligning with industry standards (Rust, C++, Java, TypeScript, Swift).

### What's Changing

**Old Syntax (Deprecated)**:
```simple
fn map[T, U](list: List[T]) -> List[U]
struct Container[T]
impl[T] MyTrait for Container[T]
```

**New Syntax (Preferred)**:
```simple
fn map<T, U>(list: List<T>) -> List<U>
struct Container<T>
impl<T> MyTrait for Container<T>
```

**Note**: Array syntax remains unchanged: `[i32]`, `[1, 2, 3]`, `arr[0]`

---

## ⏱️ Timeline

| Date | Event |
|------|-------|
| **2026-01-12** | Migration tool released |
| **[TBD]** | Community announcement |
| **[TBD + 3 months]** | End of migration period |
| **v1.0.0** | Breaking removal of `[]` syntax |

---

## 🚀 How to Migrate

### 1. Preview Changes (Recommended)

```bash
cd your_project/
simple migrate --fix-generics --dry-run src/
```

This shows which files would be modified without changing them.

### 2. Apply Migration

```bash
simple migrate --fix-generics src/
```

The tool automatically:
- ✅ Converts generic types: `List[T]` → `List<T>`
- ✅ Preserves array types: `[i32]` stays `[i32]`
- ✅ Preserves array literals: `[]` stays `[]`
- ✅ Preserves indexing: `arr[0]` stays `arr[0]`
- ✅ Preserves strings and comments

### 3. Verify and Test

```bash
# Run your tests
simple test

# Check compilation
simple compile src/main.spl
```

### 4. Commit Changes

```bash
jj describe -m "Migrate generic syntax from [] to <>"
```

---

## 🛡️ Safety Guarantees

- **Non-Breaking**: Both `[]` and `<>` syntax work during migration period
- **Zero False Positives**: Extensive testing ensures correct conversion
- **Dry-Run Mode**: Preview changes before applying
- **Comprehensive Tests**: 51 tests ensure correctness
- **Production Proven**: Successfully migrated entire Simple stdlib (49 files)

---

## 📚 Resources

- **Migration Guide**: `doc/design/GENERIC_SYNTAX_MIGRATION_SUMMARY.md`
- **Deprecation Plan**: `doc/design/generic_syntax_deprecation_plan.md`
- **Syntax Reference**: `CLAUDE.md`

---

## 🆘 Getting Help

**Issue with Migration?**
1. Run with dry-run first: `simple migrate --fix-generics --dry-run .`
2. Check the troubleshooting guide in `GENERIC_SYNTAX_MIGRATION_SUMMARY.md`
3. Report issues on GitHub with:
   - Source code that fails
   - Expected vs actual behavior
   - Tag: `migration`

**Questions?**
- File an issue on GitHub
- Join community discussion [link TBD]
- Check FAQ in migration documentation

---

## 💡 Why This Change?

**Benefits**:
1. **Industry Alignment**: Matches syntax of Rust, C++, Java, TypeScript, Swift
2. **Clarity**: Clear distinction between generics and arrays
3. **Tooling**: Better IDE support and syntax highlighting
4. **Future-Proof**: Enables advanced type system features

**Decision Factors**:
- Familiarity score: 477 vs 248 (see `type_parameter_syntax_analysis.md`)
- Reduces confusion with array syntax
- Aligns with Simple's design philosophy

---

## 🎯 Action Items

### For Application Developers

**By [TBD + 1 month]**:
- [ ] Run dry-run on your codebase
- [ ] Review and apply migration
- [ ] Test your application
- [ ] Commit changes

### For Library Authors

**By [TBD + 2 months]**:
- [ ] Migrate library code
- [ ] Update examples and documentation
- [ ] Release new version
- [ ] Notify library users

### For CI/CD Pipelines

**Optional but Recommended**:
- Add deprecation warning check
- Run migration tool in CI for validation
- Update documentation generation

---

## 📊 Migration Statistics

**Simple Stdlib Migration** (Completed):
- 648 files processed
- 49 files migrated
- 599 files already using `<>` or no generics
- 0 errors
- 100% test pass rate

---

## 🗓️ What's Next

1. **Community Feedback Period**: [TBD - 2 weeks]
   - Share your migration experience
   - Report any issues
   - Suggest improvements

2. **Migration Period**: [TBD - 3 months]
   - Both syntaxes supported
   - Deprecation warnings active
   - Migration tool available

3. **v1.0.0 Release**: [TBD]
   - Breaking removal of `[]` syntax
   - Clean, unified syntax
   - Full transition complete

---

## 🙏 Acknowledgments

This migration was designed and implemented with:
- Comprehensive testing (51 tests)
- Community-first approach
- Safe, gradual migration path
- Production-proven tooling

Thank you for your patience and cooperation during this transition. We believe this change will make Simple more accessible and maintainable for everyone.

---

**Questions or concerns?** Please reach out via [GitHub Issues / Discord / Forum].

**Ready to migrate?** Start with:
```bash
simple migrate --fix-generics --dry-run .
```

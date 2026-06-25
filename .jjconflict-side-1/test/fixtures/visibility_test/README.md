# Visibility Test Fixtures

Test files for module visibility system.

## Files

- `test_case.spl` - Module with mixed visibility
  - `TestCase` - Auto-public (matches filename)
  - `Helper` - Private (no match, no pub)
  - `Utils` - Explicitly public (pub keyword)
  - Constants and functions with various visibility

- `other.spl` - Module that imports from test_case
  - Should successfully import `TestCase` and `Utils`
  - Should warn if trying to import `Helper`

## Expected Behavior

When compiling `other.spl`:
- ✅ `use test_case.TestCase` - Works (auto-public)
- ✅ `use test_case.Utils` - Works (explicit pub)
- ⚠️ `use test_case.Helper` - Warning W0401 (private)

## Testing

```bash
# Compile individual files
simple compile test_case.spl
simple compile other.spl

# Run tests
simple test test_visibility_spec.spl
```

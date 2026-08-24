# Query DEPR002 Lexical Detection Specification

The query lint scanner must recognize `.new(` only in executable source text.
Single-line and triple-quoted string payloads plus comments are excluded before
matching while the scanner retains original one-based source coordinates.

The paired executable specifications prove:

- indented `Point.new(...)` reports column 18;
- `.new(` inside a string reports no candidate;
- `.new(` inside a comment reports no candidate;
- a real call before a trailing comment wins over comment payload.
- mixed lexical input emits exactly one JSON diagnostic at line 3, column 18.
- multiline docstrings suppress interior matches and resume after closing;
- same-line strings/docstrings resume at the exact real-code column.

Static source review confirms production diagnostics, JSON collection, and both
code-action routes consume the same request-local column projection. No manual
execution was performed under the user override.

## Executable reproductions

```simple
expect(deprecated_new_column("    val p = Point.new(1, 2)")).to_equal(18)
expect(deprecated_new_column("    val note = \"Point.new(1, 2)\"")).to_equal(0)
expect(deprecated_new_column("    # migrate Point.new(1, 2)")).to_equal(0)
```

```simple
val lines = ["val doc = \"\"\"", "Fake.new()", "\"\"\"", "    val p = Point.new()"]
expect(deprecated_new_columns(lines)).to_equal([0, 0, 0, 18])
```

```simple
val source = "# Fake.new()\nval note = \"Fake.new()\"\n    val p = Point.new()"
val result = _collect_lint_diagnostics_json("sample.spl", source)
expect(result.0).to_equal(1)
expect(result.1).to_equal("{\"severity\":2,\"code\":\"DEPR002\",\"message\":\"'.new()' constructor is deprecated\",\"line\":3,\"col\":18,\"end_line\":3,\"end_col\":23,\"tags\":[2],\"source\":\"simple-lint\"}")
```

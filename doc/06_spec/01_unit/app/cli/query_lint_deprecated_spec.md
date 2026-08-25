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
- requested-line projection preserves prefix triple-string state, exact columns,
  and invalid-index zero behavior without constructing all line columns;
- both code-action owners use the scalar projection and no longer loop over
  every source line for postprocessing.

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

```simple
val lines = [
    "# Fake.new()", "val docs = \"\"\"", "Fake.new()",
    "\"\"\"; val p = Point.new()", "val later = Other.new()"]
expect(deprecated_new_column_at(lines, 2)).to_equal(0)
expect(deprecated_new_column_at(lines, 3)).to_equal(19)
expect(deprecated_new_column_at(lines, -1)).to_equal(0)
expect(deprecated_new_column_at(lines, lines.len())).to_equal(0)
```

The executable owner-wiring scenario reads both
`src/app/cli/query_commands.spl` and `src/app/cli/query_navigation.spl`, bounds
each `query_code_actions` source region, and requires:

``` text
deprecated_new_column_at(source_lines, sli)
val sli = line_num - 1
```

It rejects `deprecated_new_columns(` and the former
`while sli < source_lines.len()` loop within both bounded regions. This is a
structural routing contract; semantic behavior remains pinned by the scalar
projection examples above.

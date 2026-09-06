# Query Safety Lint Lexical Projection Specification

SAFE001 and SAFE003 are severity-one diagnostics, so only executable source may
affect their emission or `unsafe` scope. A request-local lexical projection
tracks ordinary strings, escapes, comments, and triple-quoted strings once and
records first-code plus bounded-pattern columns for each physical line.

The canonical executable specification proves:

- a real indented `ptr_read(` produces one exact SAFE003 object at columns
  13–22;
- comments, strings, and docstrings do not emit pointer errors;
- fake `unsafe:` payload cannot suppress a later real pointer error;
- real unsafe blocks continue to suppress their pointer operations;
- scanning resumes after multiline and same-line triple-string closure;
- two pointer operations produce one SAFE003 at the first real token;
- SAFE001 applies the same lexical boundary and exact token span.

```simple
val diagnostics = _safety_diagnostics([
    "fn probe():", "    val x = ptr_read(handle)"])
expect(diagnostics).to_equal([
    "{\"severity\":1,\"code\":\"SAFE003\",\"message\":\"raw pointer operation outside unsafe block\",\"line\":2,\"col\":13,\"end_line\":2,\"end_col\":22,\"tags\":[],\"source\":\"simple-lint\"}"])
```

```simple
val diagnostics = _safety_diagnostics([
    "fn probe():", "    \"\"\"", "unsafe:", "ptr_read(handle)",
    "    \"\"\"", "    ptr_read(handle)"])
expect(diagnostics.len()).to_equal(1)
expect(diagnostics[0]).to_contain("\"line\":6,\"col\":5")
```

```simple
val fake_unsafe = _safety_diagnostics([
    "fn probe():", "    val note = \"unsafe:\"", "    # unsafe:",
    "    ptr_read(handle)"])
expect(fake_unsafe.len()).to_equal(1)

val real_unsafe = _safety_diagnostics([
    "fn probe():", "    unsafe:", "        ptr_read(handle)",
    "    val done = true"])
expect(real_unsafe.len()).to_equal(0)
```

```simple
val nested = _safety_diagnostics([
    "fn probe():", "    unsafe:", "        unsafe:",
    "            ptr_read(a)", "        ptr_read(b)", "    ptr_read(c)"])
expect(nested.len()).to_equal(1)
expect(nested[0]).to_contain("\"line\":6,\"col\":5")

val prefixed = _safety_diagnostics([
    "fn probe():", "    unsafe:", "        ptr_read(a)",
    "    unsafe_value = 0", "    ptr_read(b)"])
expect(prefixed.len()).to_equal(1)
```

```simple
val same_line = _safety_diagnostics([
    "fn probe():", "    \"\"\"Fake ptr_read(x)\"\"\"; ptr_write(x)"])
expect(same_line[0]).to_contain(
    "\"col\":29,\"end_line\":2,\"end_col\":39")

val first = _safety_diagnostics([
    "fn probe():", "    val x = ptr_write(a) + ptr_read(b)"])
expect(first[0]).to_contain(
    "\"col\":13,\"end_line\":2,\"end_col\":23")
```

```simple
val operations = [
    "ptr_read(", "ptr_write(", "ptr_cast(", "ptr_offset(",
    "mem_copy(", "mem_set("]
for operation in operations:
    val diagnostics = _safety_diagnostics([
        "fn probe():", "    {operation}handle)"])
    expect(diagnostics.len()).to_equal(1)
    expect(diagnostics[0]).to_contain("\"col\":5")
    expect(diagnostics[0]).to_contain(
        "\"end_col\":{5 + operation.len()}")
```

```simple
val assembly = _safety_diagnostics([
    "fn probe():", "    # asm(\"nop\")", "    val note = \"asm nop\"",
    "    \"\"\"", "asm(\"fake\")", "    \"\"\"", "    asm(\"nop\")"])
expect(assembly).to_equal([
    "{\"severity\":1,\"code\":\"SAFE001\",\"message\":\"inline assembly outside unsafe block\",\"line\":7,\"col\":5,\"end_line\":7,\"end_col\":9,\"tags\":[],\"source\":\"simple-lint\"}"])
```

No manual execution or runtime/RSS measurement was performed under the user
override.

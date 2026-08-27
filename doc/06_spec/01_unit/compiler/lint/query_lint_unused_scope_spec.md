# Query lint UNUSED001 scope specification

> Source-reviewed, manually unverified regression contract for sibling/dedent
> scope isolation, blank/deeper-body retention, callable-prefix recognition,
> exact warning cardinality/order, and indented JSON spans.

## Required scenarios

The paired executable specs contain six source-reviewed scenarios:

1. A sibling-method reference cannot suppress the first method's unused local;
   the two warnings appear in source order on lines 3 and 5.
2. A same-method reference suppresses its own declaration while an unused local
   in the sibling still warns.
3. A module-level function after a class dedent cannot contribute a use to the
   preceding method.
4. Blank lines and deeper conditional bodies remain inside the method scope.
5. Representative `pub fn` and `async fn` headers receive UNUSED001 analysis.
6. A one-character binding named `a` reports the binding token, not the `a`
   inside `val`.

## Sibling methods are separate identifier scopes

```simple
val source = "class ScopeProbe:\n" +
    "    fn first():\n" +
    "        val used_elsewhere = 1\n" +
    "    fn second():\n" +
    "        val copy = used_elsewhere\n"
val records = _unused_records(source)
expect(records.len()).to_equal(2)
expect(records[0]).to_contain(
    "variable 'used_elsewhere' is declared but never used")
expect(records[1]).to_contain("variable 'copy' is declared but never used")
```

## Same-method uses remain local

```simple
val source = "class ScopeProbe:\n" +
    "    fn first():\n" +
    "        val kept = 1\n" +
    "        print kept\n" +
    "    fn second():\n" +
    "        val unused_b = 2\n"
val records = _unused_records(source)
expect(records.len()).to_equal(1)
expect(records[0]).to_contain("variable 'unused_b' is declared but never used")
expect(records[0].contains("variable 'kept'")).to_equal(false)
```

## Shallower dedents terminate the method

```simple
val source = "class ScopeProbe:\n" +
    "    fn first():\n" +
    "        val method_only = 1\n" +
    "fn module_fn():\n" +
    "    print method_only\n"
val records = _unused_records(source)
expect(records.len()).to_equal(1)
expect(records[0]).to_contain("variable 'method_only' is declared but never used")
```

## Blank lines and deeper blocks remain inside the method

```simple
val source = "class ScopeProbe:\n" +
    "    fn first():\n" +
    "        val nested_use = 1\n\n" +
    "        if true:\n" +
    "            print nested_use\n"
expect(_unused_records(source).len()).to_equal(0)
```

## Representative public and asynchronous headers are analyzed

```simple
val source = "pub fn public_probe():\n" +
    "    val public_unused = 1\n" +
    "async fn async_probe():\n" +
    "    val async_unused = 2\n"
val records = _unused_records(source)
expect(records.len()).to_equal(2)
expect(records[0]).to_contain("variable 'public_unused' is declared but never used")
expect(records[1]).to_contain("variable 'async_unused' is declared but never used")
```

## JSON spans use original source columns

```simple
val source = "class ScopeProbe:\n" +
    "    fn first():\n" +
    "        val a = 1\n"
val records = _unused_records(source)
expect(records.len()).to_equal(1)
expect(records[0]).to_contain("variable 'a' is declared but never used")
expect(records[0]).to_contain("\"line\":3,\"col\":13")
expect(records[0]).to_contain("\"end_line\":3,\"end_col\":14")
```

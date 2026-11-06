# `.?` on `Some("")` (text? holding the empty string) is false/nil on the seed interpreter

**Status:** OPEN (seed interpreter; found 2026-11-06 while un-stubbing core_intensive_spec)

Probe:
```
fn f() -> text?:
    Some("")
val a = f()
print "a={a.?}"      # prints a=nil, expected a=true
```
`val b: text? = Some("x")` -> `b.?` is truthy. Only the empty payload collapses.
Impact: `StringInterner.lookup(id)` for an interned `""` reports no value, so
`test/02_integration/compiler/core_intensive_spec.spl` "handles empty string"
(`check(lookup.?)`) fails. The lib returns the right `Some("")`
(`lookup(id)? == ""` is true). The spec is correct; do not weaken it.
Fix lives in the seed `.?` / Option presence test (src/compiler_rust interpreter).

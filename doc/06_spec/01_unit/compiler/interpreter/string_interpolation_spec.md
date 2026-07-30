# Self-hosted interpreter string interpolation

Status: executable SSpec added; qualified pure-Simple execution pending.

## evaluates variables expressions and multiple regions

- Define integer values and a text array.
- Evaluate bare, expression, repeated, and nested-string interpolation.
- Expect exact substituted text for every result.

<details>
<summary>Executable SSpec</summary>

```simple
val a = 2
val b = 3
val words = ["a", "b"]

expect("bare={a}").to_equal("bare=2")
expect("expr={a + b}").to_equal("expr=5")
expect("nested {a} and {b}").to_equal("nested 2 and 3")
expect("joined={words.join("-")}").to_equal("joined=a-b")
expect("{{literal}} {a}").to_equal("{literal} 2")
```

</details>

## keeps escaped and non-expression braces literal

- Decode doubled brace escapes.
- Preserve a CSS-shaped brace region that is not a valid expression.

<details>
<summary>Executable SSpec</summary>

```simple
val escaped = "{{not interpolation}}"
val css = "{ color: red; }"
val mixed_invalid = "before {value} then { color: red; }"
val after = 9

expect(escaped).to_equal("{" + "not interpolation" + "}")
expect(css).to_equal("{" + " color: red; " + "}")
expect(mixed_invalid).to_equal(
    "before " + "{value}" + " then " + "{ color: red; }"
)
expect(after).to_equal(9)
```

</details>

## does not interpolate raw strings

- Read a raw string containing braces.
- Expect the original literal content.

<details>
<summary>Executable SSpec</summary>

```simple
val value = 7
val raw = r"{value}"

expect(raw).to_equal("{" + "value" + "}")
```

</details>

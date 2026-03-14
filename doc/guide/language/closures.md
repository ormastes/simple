# Closures & Functional Patterns

This chapter covers Simple's functional programming features: lambdas, iterators, composition operators, and comprehensions.

## Lambdas

### Explicit Parameter

```simple
items.map(\x: x * 2)
items.filter(\x: x > 0)
```

### Placeholder Lambda

```simple
items.map(_ * 2)           # _ is the single parameter
items.filter(_ > 0)
```

### Numbered Placeholders

```simple
pairs.map(_1 + _2)         # _1 = first param, _2 = second
```

### Method Reference

```simple
words.map(&:len)            # Equivalent to \x: x.len()
names.map(&:upper)
```

## Iterator Methods

Common iterator methods on collections:

```simple
val numbers = [1, 2, 3, 4, 5]

numbers.map(_ * 2)              # [2, 4, 6, 8, 10]
numbers.filter(_ > 3)           # [4, 5]
numbers.reduce(0, _1 + _2)     # 15
numbers.any(_ > 4)              # true
numbers.all(_ > 0)              # true
numbers.find(_ == 3)            # Some(3)
numbers.take(3)                 # [1, 2, 3]
numbers.skip(2)                 # [3, 4, 5]
numbers.zip(other)              # [(1,a), (2,b), ...]
```

## Comprehensions

```simple
[for x in 0..10: x * x]                      # [0, 1, 4, 9, ...]
[for x in 0..10 if x % 2 == 0: x]            # [0, 2, 4, 6, 8]
[for x in xs for y in ys: (x, y)]            # Nested
```

## Pipe Operator

```simple
data
    |> parse
    |> validate
    |> transform
    |> save
```

## Compose Operator

```simple
val process = parse >> validate >> transform
process(data)
```

## Closure Capture

Closures can **read** outer variables but **cannot modify** them (nested closure limitation):

```simple
val multiplier = 3
items.map(_ * multiplier)     # OK: reads multiplier

var count = 0
# items.each(\x: count = count + 1)  # ERROR: cannot modify outer var
```

Module-level closures can modify module-level `var`s.

## See Also

- [Syntax](syntax.md) for operator precedence
- [Collections](../library/collections.md) for collection types and their methods
- [Control Flow](control_flow.md) for iteration constructs

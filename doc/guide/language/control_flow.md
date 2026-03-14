# Control Flow & Pattern Matching

This chapter covers Simple's control flow constructs and pattern matching system.

## Conditionals

### if / else

```simple
if x > 0:
    print "positive"
else if x == 0:
    print "zero"
else:
    print "negative"
```

### if val (Pattern Binding)

```simple
if val user = find_user(id):
    print "Found: {user.name}"
else:
    print "Not found"
```

### Multi-line Conditions

Wrap in parentheses for multi-line boolean expressions:

```simple
if (is_valid and
    not expired):
    process()
```

## Pattern Matching

### match

```simple
match value:
    Some(x): process(x)
    nil: default_value()
```

### Match with Guards

```simple
match score:
    x if x >= 90: "A"
    x if x >= 80: "B"
    x if x >= 70: "C"
    _: "F"
```

### Enum Matching

```simple
match result:
    Ok(value): use(value)
    Err(e): handle(e)
```

## Loops

### for

```simple
for item in items:
    process(item)

for i in 0..10:
    print i
```

### while

```simple
while condition():
    step()
```

### loop

```simple
loop:
    val line = read_line()
    if line == "quit":
        break
    process(line)
```

## Optional Chaining

```simple
user?.address?.city ?? "Unknown"
```

## See Also

- [Syntax](syntax.md) for expression-level constructs
- [Type System](type_system.md) for algebraic types used in matching
- [Error Handling](error_handling.md) for `Result` matching patterns

# Simple Collections Tutorial

This tutorial demonstrates the Stack data structure in Simple.

## Creating a Stack

You can create a new stack with `Stack.new()`:

```simple-doctest
>>> stack = Stack.new()
>>> stack.is_empty()
True
```

## Pushing Items

Use `push()` to add items:

```simple-doctest
>>> stack = Stack.new()
>>> stack.push(10)
>>> stack.push(20)
```

## Popping Items

Use `pop()` to remove and return items:

```simple-doctest
>>> stack = Stack.new()
>>> stack.push(100)
>>> stack.pop()
100
>>> stack.is_empty()
True
```

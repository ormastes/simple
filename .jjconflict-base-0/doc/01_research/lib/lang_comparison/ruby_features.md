# Ruby-Inspired Features

Status: production API contract.

Simple should borrow Ruby's expressiveness where it improves everyday code, but
not Ruby's implicit global state, unchecked exceptions, or surprise mutation.

## Adopt

| Ruby idea | Simple contract |
| --- | --- |
| Short collection verbs | Provide `each`, `map`, `select`, `reject`, `find`, `group_by`, `sort_by` on collection-like types. |
| Blocks as readable pipelines | Prefer block-friendly APIs when they keep the call site linear and obvious. |
| Predicate readability | Prefer `empty.?`, `present.?`, `valid.?`, `success.?` for public predicates. |
| Bang-like distinction | Use explicit `_in_place` / `must_` naming instead of punctuation suffixes. |
| `fetch` semantics | `fetch` means missing key/index is an error or caller-provided default; `get` remains optional. |
| Enumerable consistency | Similar receiver types should share the same verb set and ordering. |
| Hash/array literals | Keep APIs friendly to literal maps/lists and named arguments. |

## Do Not Adopt

- Implicit exceptions as normal control flow. Use `Result<T, E>` and `?`.
- Monkey patching or runtime reopening of core types.
- Method names whose only meaning comes from punctuation.
- Hidden mutation in a method that looks like a query.
- Global process state that changes parser, compiler, or runtime behavior.

## API Shape Examples

Preferred:

```spl
val names = users.select(fn user: user.active.?).map(fn user: user.name)
val port = env.fetch("PORT").parse_int()?
buffer.replace_range_in_place(start, finish, text)
```

Avoid:

```spl
val names = users.filter_active_users_and_extract_names()
val port = env.get("PORT").unwrap().to_i()
buffer.replace_range(start, finish, text) # ambiguous mutation
```

## Method Families Required for Production Collections

Any public collection-like type should document whether it supports:

- Traversal: `each`, `iter`
- Transformation: `map`, `flat_map`
- Filtering: `select`, `reject`
- Query: `any.?`, `all.?`, `empty.?`, `includes.?`
- Lookup: `get`, `fetch`
- Conversion: `to_array`, `to_map`, `as_slice` where applicable
- Mutation: `push`, `append`, `remove`, `clear`, with `_in_place` when mutation
  is not obvious from the receiver type

Partial support is acceptable only when the type documents the reason, such as
noalloc, streaming, single-pass, or persistent immutable constraints.

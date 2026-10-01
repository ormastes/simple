# Interpreter detaches inner-array aliases of a global `[[T]]`; element writes on the alias are lost

- Status: OPEN (2026-09-26)
- Host: this Linux aarch64 box, deployed compiler `bin/simple`
  (Rust seed interpreter, `--mode=interpreter`)
- Found while building the SOSIX stdio slice
  (`src/os/services/sosix/stdio_v1.spl`, lane codex/spipe-local-knowledge-setup).

## Symptom

Given a module-global array-of-arrays, binding an inner array to a local
and then index-assigning into the local fails or silently loses writes,
depending on whether the inner array was empty at bind time:

```spl
var _files: [[u8]] = []

fn _alias_write_no_push():
    var content = _files[0]     # alias of the inner array
    content[0] = 90             # ERROR: invalid assignment:
                                # cannot index assign value of type array

fn _alias_write_lost():
    var content = _files[0]
    content.push(0)             # push succeeds (on a detached copy)
    content[0] = 90             # lands on the detached copy
    # _files[0] is UNCHANGED here unless the copy is stored back
```

Observed behavior (probe specs under /tmp, 2026-09-26):

- `_files = [text_to_bytes("abc")]` → `var c = _files[0]; c[0] = 90`
  errors with "invalid assignment: cannot index assign value of type array"
  (the container is a plain `[u8]`, not an object lacking `__setitem__`).
- The same bind after `_files[0] = []` (fresh empty literal in the slot)
  works, including `push` + index-assign + store-back.
- After `content.push(...)`, further mutations land only on the detached
  local copy; the global slot keeps the old value unless the copy is
  stored back explicitly.

## Impact

Any fake/backend that models storage as `[[u8]]` and does
`var content = global[i]; content[j] = b; global[i] = content` hits this
as soon as the stored inner array is non-empty and no `push` precedes the
index write. The SOSIX stdio spec
(`test/01_unit/os/services/sosix_stdio_v1_spec.spl`) works around it with
functional copy-back: build the new inner array by pushes into a fresh
local, then store it back into the global slot.

## Expected

`var content = global[i]` should either alias coherently (writes visible
through both paths) or deep-copy at bind time (writes visible in the
local only, consistently) — never an error for a plain array container
nor partially-lost mutations.

## Repro

`test/01_unit/os/services/sosix_stdio_v1_spec.spl` at the pre-workaround
revision (fake `_write` with `var content = _files[index]` + in-place
element writes); minimal probes in the session log of the stdio slice.

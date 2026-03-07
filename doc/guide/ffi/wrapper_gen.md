# Wrapper Generator

**Status:** Planned (Not Yet Implemented)

---

## Overview

`simple wrapper-gen` will automatically generate all three tiers of SFFI wrappers from a single specification file. This eliminates manual boilerplate when wrapping external C/C++ libraries.

---

## Quick Start

```bash
# Generate wrappers from spec
simple wrapper-gen specs/my_library.spec

# Preview without writing files
simple wrapper-gen specs/my_library.spec --dry-run

# Generate specific tier only
simple wrapper-gen specs/my_library.spec --tier=3
```

---

## Spec File Format

```spec
# specs/my_library.spec
library: my_library
include: "my_library.h"
link: "-lmylib"

# Function declarations
fn create() -> handle
fn process(h: handle, data: text) -> i32
fn destroy(h: handle) -> void

# Type mappings
type handle = void*    # Maps to i64 in Simple
type matrix = void*    # Opaque handle
```

### Supported Types

| Spec Type | C Type | Simple Type |
|-----------|--------|-------------|
| `i32` | `int32_t` | `i32` |
| `i64` | `int64_t` | `i64` |
| `f32` | `float` | `f32` |
| `f64` | `double` | `f64` |
| `bool` | `bool` | `bool` |
| `text` | `const char*` | `text` |
| `handle` | `void*` | `i64` |
| `void` | `void` | `()` |

### Ownership Annotations

```spec
fn create() -> handle [own]           # Caller owns returned handle
fn process(h: handle [borrow]) -> i32 # Borrows, does not free
fn destroy(h: handle [consume]) -> void  # Consumes (frees) the handle
```

| Annotation | Meaning |
|-----------|---------|
| `[own]` | Caller receives ownership, must free |
| `[borrow]` | Temporary access, do not free |
| `[consume]` | Callee takes ownership, frees internally |

---

## Generated Output

From a single spec, the generator produces three files:

### Tier 1: C Glue (`src/lib/ffi/my_library_glue.c`)

```c
#include "my_library.h"

void* spl_my_library_create() {
    return my_library_create();
}

int spl_my_library_process(void* h, const char* data) {
    return my_library_process(h, data);
}

void spl_my_library_destroy(void* h) {
    my_library_destroy(h);
}
```

### Tier 2: FFI Declarations (`src/lib/ffi/my_library.spl`)

```simple
extern fn spl_my_library_create() -> i64
extern fn spl_my_library_process(handle: i64, data: text) -> i32
extern fn spl_my_library_destroy(handle: i64)
```

### Tier 3: Safe API (`src/lib/my_library/mod.spl`)

```simple
use std.ffi.my_library.{
    spl_my_library_create,
    spl_my_library_process,
    spl_my_library_destroy
}

class MyLibrary:
    handle: i64

    static fn create() -> MyLibrary:
        MyLibrary(handle: spl_my_library_create())

    fn process(data: text) -> i32:
        spl_my_library_process(self.handle, data)

    fn destroy():
        spl_my_library_destroy(self.handle)
```

---

## Real-World Example: PyTorch

### Spec File

```spec
library: torch
include: "torch/torch.h"
link: "-ltorch -lc10"

fn tensor_zeros(rows: i32, cols: i32) -> handle [own]
fn tensor_ones(rows: i32, cols: i32) -> handle [own]
fn tensor_add(a: handle [borrow], b: handle [borrow]) -> handle [own]
fn tensor_matmul(a: handle [borrow], b: handle [borrow]) -> handle [own]
fn tensor_numel(t: handle [borrow]) -> i64
fn tensor_to_cuda(t: handle [borrow], device: i32) -> handle [own]
fn tensor_is_cuda(t: handle [borrow]) -> bool
fn tensor_free(t: handle [consume]) -> void
```

### Generate

```bash
simple wrapper-gen specs/torch.spec
```

This produces all three tiers automatically, ready to use:

```simple
use std.torch.{Tensor}

fn main():
    val a = Tensor.zeros(3, 4)
    val b = Tensor.ones(3, 4)
    val c = a.add(b)
    print "Elements: {c.numel()}"
    c.free()
    b.free()
    a.free()
```

---

## Command Options

| Option | Description |
|--------|-------------|
| `--dry-run` | Preview generated code without writing |
| `--tier=N` | Generate only tier N (1, 2, or 3) |
| `--output=DIR` | Output directory (default: `src/lib/`) |
| `--force` | Overwrite existing files |
| `--no-class` | Generate functions only, no class wrapper |

---

## Best Practices

1. **Start with the spec** -- Define the API contract before writing any code
2. **Use ownership annotations** -- Prevents memory leaks and double-frees
3. **Keep specs minimal** -- Only expose functions your Simple code actually needs
4. **Review generated code** -- Auto-generated code may need manual tuning
5. **Version your specs** -- Track spec files in version control alongside source

---

## Troubleshooting

| Issue | Cause | Fix |
|-------|-------|-----|
| Type not recognized | Missing type mapping | Add `type X = C_type` to spec |
| Link error | Library not found | Check `link:` path in spec |
| Generated class conflicts | Name collision | Use `--no-class` or rename |
| Handle leak | Missing `[own]` annotation | Add ownership annotations |

---

## Related

- SFFI guide: `doc/guide/ffi/sffi.md`
- FFI module: `src/lib/ffi/mod.spl`

# backend port feature
*Source:* `test/feature/app/backend_port_feature_spec.spl`

## Behavior

### BackendPort Feature: Phase 1 - Struct shape

### When name field

- BackendPort has name field
- name field is a non-empty text

### When compile function field

- BackendPort has run_fn field
- run_fn is a callable function

### When emit function fields

- BackendPort has supports_jit_fn field
- BackendPort has target_triple_fn field
- supports_jit_fn is callable and returns bool
- target_triple_fn is callable and returns text

### BackendPort Feature: Phase 2 - Factory creation

### When noop backend factory

- noop backend has correct name
- noop backend compile fn returns result
- noop backend supports_jit_fn returns false
- noop backend target_triple_fn returns noop

### When custom backend creation

- custom backend can define its own supports_jit behavior
- custom backend can define its own target_triple
- custom backend target triple differs from noop triple

### When multiple backends

- two noop backends have same name
- two noop backends have same target triple

### BackendPort Feature: Phase 3 - Integration with CompilerServices

### When CompilerServices has backend field

- CompilerServices.backend is a BackendPort
- backend field is distinct from lexer field
- backend field is distinct from parser field
- backend field is distinct from logger field

### When backend swapping in services

- backend can be replaced with different name via delegation
- alternate backend target triple is different from noop

### When backend port functions callable end-to-end

- full chain: services -> backend -> supports_jit
- full chain: services -> backend -> target_triple
- full chain: services -> backend -> name then supports_jit

### BackendPort Feature: Phase 4 - Type safety

### When name is unique identifier

- BackendPort name is meaningful (not empty)
- noop backend name starts with noop prefix
- noop backend name contains backend suffix

### When different backends have different names

- noop backend name differs from custom name
- noop backend name differs from wasm backend name
- backend identification works via target_triple

### When fn-field type correctness

- supports_jit_fn always returns a bool
- target_triple_fn always returns a text
- calling fn-fields multiple times is idempotent



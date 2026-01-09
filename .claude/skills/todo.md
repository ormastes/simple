# TODO Skill - Comment Format Specification

## Format

```
TODO: [area][priority] description [#issue] [blocked:#issue,#issue]
FIXME: [area][priority] description [#issue] [blocked:#issue,#issue]
```

### Components

| Component | Required | Format | Examples |
|-----------|----------|--------|----------|
| Keyword | Yes | `TODO:` or `FIXME:` | `TODO:`, `FIXME:` |
| Area | Yes | `[area]` | `[runtime]`, `[stdlib]`, `[codegen]` |
| Priority | Yes | `[P0-P3]` or `[name]` | `[P0]`, `[critical]`, `[high]` |
| Description | Yes | Free text | `Implement socket write` |
| Issue | No | `[#number]` | `[#234]` |
| Blocked | No | `[blocked:#n,#m]` | `[blocked:#123,#456]` |

### Priority Levels

| Level | Aliases | Meaning |
|-------|---------|---------|
| P0 | `critical` | Blocking, fix immediately |
| P1 | `high` | Important, next sprint |
| P2 | `medium` | Should do, backlog |
| P3 | `low` | Nice to have, someday |

### Areas

| Area | Scope |
|------|-------|
| `runtime` | GC, values, monoio, concurrency |
| `codegen` | MIR, Cranelift, LLVM, Vulkan |
| `compiler` | HIR, pipeline, interpreter |
| `parser` | Lexer, AST, parsing |
| `type` | Type checker, inference |
| `stdlib` | Simple standard library |
| `gpu` | GPU/SIMD/graphics |
| `ui` | UI framework |
| `test` | Test frameworks |
| `driver` | CLI, tools |
| `loader` | SMF loader |
| `pkg` | Package manager |

## Examples

### Rust

```rust
// TODO: [runtime][P0] Implement monoio TCP write [#234]
// TODO: [runtime][critical] Fix memory barrier race [#567] [blocked:#123]
// TODO: [codegen][P1] Track line numbers in HIR [#789]
// TODO: [codegen][high] Add SPIR-V validation
// TODO: [compiler][P2] Implement SDN parsing [blocked:#100,#101]
// TODO: [parser][P3] Parse !Trait syntax [#1151]
// FIXME: [runtime][P0] Memory leak in GC barrier [#890]
// FIXME: [type][critical] Incorrect unification [#891] [blocked:#500]
```

### Simple

```simple
# TODO: [stdlib][P0] Implement via FFI [#234]
# TODO: [stdlib][critical] Fix memory corruption [#567]
# TODO: [gpu][P1] Create Vector3 variant [#789] [blocked:#100]
# TODO: [gpu][high] Implement render commands
# TODO: [stdlib][P2] Add JSON parsing [blocked:#200,#201]
# TODO: [test][P3] Add edge case tests
# FIXME: [stdlib][P0] Incorrect return value [#890]
# FIXME: [ui][critical] Layout crash [#891] [blocked:#400,#401]
```

### Multi-line (complex description)

```rust
// TODO: [runtime][P1] Implement dedicated runtime thread [#234]
//       Need message passing between main thread and monoio runtime.
//       See monoio_tcp.rs:251 for context.
//       [blocked:#100,#101]
```

```simple
# TODO: [stdlib][P1] Implement file watching [#345]
#       Need to use platform-specific APIs:
#       - Linux: inotify
#       - macOS: FSEvents
#       - Windows: ReadDirectoryChangesW
#       [blocked:#200]
```

## Quick Reference

```
TODO: [area][P0|P1|P2|P3] description [#issue] [blocked:#n,#m]
      │      │            │            │        └── Optional: blocking issues
      │      │            │            └── Optional: related issue
      │      │            └── Required: what needs to be done
      │      └── Required: P0/critical, P1/high, P2/medium, P3/low
      └── Required: runtime, codegen, compiler, parser, stdlib, gpu, etc.
```

## Regex Patterns

### Match TODO/FIXME
```regex
(TODO|FIXME):\s*\[(\w+)\]\[(\w+)\]\s*(.+?)(?:\s*\[#(\d+)\])?(?:\s*\[blocked:(#\d+(?:,#\d+)*)\])?$
```

### Capture Groups
1. Keyword (TODO/FIXME)
2. Area
3. Priority
4. Description
5. Issue number (optional)
6. Blocked issues (optional)

## Lint Rules

Enforced by `simple/app/lint/main.spl`:

| Code | Level | Description |
|------|-------|-------------|
| T001 | Warn | TODO/FIXME missing [area][priority] format |
| T002 | Warn | TODO/FIXME has invalid area |
| T003 | Warn | TODO/FIXME has invalid priority |
| T004 | Deny | P0/critical TODO must have issue number |

Run linter:
```bash
./target/debug/simple simple/app/lint/main.spl <file.spl>
```

## Migration

**Script:** `scripts/simple/migrate_todo.spl`

```bash
# Dry run (preview changes)
./target/debug/simple scripts/simple/migrate_todo.spl src/compiler/ --dry-run

# Migrate with verbose output
./target/debug/simple scripts/simple/migrate_todo.spl src/runtime/ --verbose

# Migrate single file
./target/debug/simple scripts/simple/migrate_todo.spl src/compiler/src/mock.rs
```

**Manual conversion:**
```
# Old
// TODO: Implement socket write

# New
// TODO: [runtime][P2] Implement socket write
```

## See Also

- `simple/TODO.md` - Project TODO list
- `doc/status/` - Feature implementation status
- `.claude/skills/debug.md` - Debugging skill

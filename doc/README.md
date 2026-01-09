# Simple Language Documentation

Documentation for the Simple language compiler.

## Directory Structure

```
doc/
├── README.md
│
├── feature/           # GENERATED - from feature_db.sdn
│   ├── feature_db.sdn # Feature database
│   ├── feature.md     # Generated summary
│   └── category/      # Generated category files
│
├── task/              # GENERATED - from task_db.sdn
│   ├── task_db.sdn    # Task database (non-feature work)
│   └── task.md        # Generated summary
│
├── spec/              # GENERATED - from tests/spec/*_spec.spl
│   ├── generated/     # Auto-generated specs
│   ├── parser/        # Parser reference
│   ├── tooling/       # Tool specs
│   ├── testing/       # Test framework specs
│   ├── gpu_simd/      # GPU specs
│   └── graphics_3d/   # 3D rendering specs
│
├── architecture/      # Architecture overview
├── design/            # Design documents
├── research/          # Exploratory research
├── plan/              # Implementation roadmaps
├── guide/             # How-to guides
├── example/           # Code examples
├── report/            # Session logs
└── archive/           # Retired documents
```

## Generated vs Manual

| Directory | Source | Generated? |
|-----------|--------|------------|
| `feature/` | `feature_db.sdn` | Yes |
| `task/` | `task_db.sdn` | Yes |
| `spec/generated/` | `tests/spec/*_spec.spl` | Yes |
| `architecture/` | Manual | No |
| `design/` | Manual | No |
| `research/` | Manual | No |
| `plan/` | Manual | No |
| `guide/` | Manual | No |
| `example/` | Manual | No |
| `report/` | Manual | No |
| `archive/` | Manual | No |

## Workflow

### Feature Development
1. Add feature to `feature/feature_db.sdn`
2. Write spec in `tests/spec/*_spec.spl`
3. Run `simple feature-gen` → generates `feature/feature.md`
4. Run `simple spec-gen` → generates `spec/generated/`

### Task Management
1. Add task to `task/task_db.sdn`
2. Run `simple task-gen` → generates `task/task.md`
3. Update status as work progresses

## Database Formats

### feature_db.sdn
```
features |id, category, name, description, spec, status, valid|
    1, Category, "Name", "Description", doc/spec/file.md, complete, true
```

### task_db.sdn
```
tasks |id, category, name, description, priority, status, valid|
    1, Category, "Name", "Description", high, planned, true
```

## Related

- `../verification/` - Lean 4 formal verification
- `../tests/spec/` - Executable specifications (`*_spec.spl`)
- `../src/` - Compiler source code

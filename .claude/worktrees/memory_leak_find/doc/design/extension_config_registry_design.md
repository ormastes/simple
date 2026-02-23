# Extension-Config Registry Design

**Date:** 2026-02-01
**Status:** Proposal

## Summary

A unified registry that maps file extensions to their compilation/execution configuration: compiler backend, default imports, script mode, and associated DSL packages. This generalizes the existing convention-based file type detection into an explicit, extensible system.

```simple
# Registry entries (conceptual)
extension_config:
    .spl:
        compiler: simple_compiler
        prelude: std.prelude
        mode: module

    .sdn:
        compiler: sdn_compiler
        prelude: none
        mode: data

    .ssh:
        compiler: simple_compiler
        prelude: std.prelude
        default_imports: [std.shell.*]
        mode: script
        interpreter: true
```

## Motivation

Currently, file type behavior is scattered across convention-based checks:

- `.spl` files: compiled by Simple compiler, prelude auto-imported
- `.sdn` files: parsed by `simple_sdn` crate (Rust), no compilation
- `_spec.spl` files: BDD functions auto-registered via thread-local storage
- `_test.spl` files: test harness context

Adding `.ssh` (Simple Shell) requires yet another special case. Instead, a registry maps extensions to their configuration, making the system explicit and extensible.

## Design

### Extension Config Entry

```simple
struct ExtensionConfig:
    extension: text                    # ".spl", ".sdn", ".ssh"
    compiler: CompilerBackend          # which compiler/parser
    prelude: Option<text>              # prelude module path (or none)
    default_imports: [text]            # auto-imported packages
    mode: FileMode                     # module, script, data
    interpreter: bool                  # run via interpreter (not codegen)
    lint_profile: Option<text>         # lint rules to apply

enum CompilerBackend:
    SimpleCompiler                     # full Simple compiler
    SdnCompiler                        # SDN data parser
    ShellCompiler                      # Simple + shell DSL extensions

enum FileMode:
    Module                             # normal module compilation
    Script                             # top-level statements, no module wrapper
    Data                               # data file, no execution
```

### Registry

```simple
# Built-in registry (hardcoded defaults)
val EXTENSION_REGISTRY = {
    ".spl": ExtensionConfig(
        extension: ".spl",
        compiler: CompilerBackend.SimpleCompiler,
        prelude: Some("std.prelude"),
        default_imports: [],
        mode: FileMode.Module,
        interpreter: false,
        lint_profile: Some("default"),
    ),
    ".sdn": ExtensionConfig(
        extension: ".sdn",
        compiler: CompilerBackend.SdnCompiler,
        prelude: None,
        default_imports: [],
        mode: FileMode.Data,
        interpreter: false,
        lint_profile: None,
    ),
    ".ssh": ExtensionConfig(
        extension: ".ssh",
        compiler: CompilerBackend.SimpleCompiler,
        prelude: Some("std.prelude"),
        default_imports: ["std.shell.*"],
        mode: FileMode.Script,
        interpreter: true,
        lint_profile: Some("shell"),
    ),
}
```

### Naming Pattern Overrides

For `_spec.spl` and `_test.spl`, the base `.spl` config is extended:

```simple
# Pattern-based overrides (applied on top of extension config)
val PATTERN_OVERRIDES = {
    "*_spec.spl": PatternOverride(
        additional_imports: ["std.test.bdd.*"],
        lint_profile: Some("spec"),
    ),
    "*_test.spl": PatternOverride(
        additional_imports: ["std.test.*"],
        lint_profile: Some("test"),
    ),
}
```

### Resolution Order

1. Look up extension in `EXTENSION_REGISTRY`
2. Check filename against `PATTERN_OVERRIDES`
3. Merge: override additions layer on top of extension config
4. Apply prelude (unless `#[no_prelude]`)
5. Apply default_imports
6. Apply lint_profile

## How `.sdn` Connects

`.sdn` files currently use the Rust `simple_sdn` crate directly. With the registry:

- Extension `.sdn` maps to `CompilerBackend.SdnCompiler`
- No prelude, no default imports, mode `Data`
- The SDN compiler parses the data format and returns structured values
- Script config files (`simple.sdn`) are loaded via this path

This unifies `.sdn` handling under the same dispatch mechanism as `.spl` and `.ssh`.

## How `.ssh` Connects

`.ssh` files use the full Simple compiler but with:

- `default_imports: ["std.shell.*"]` — shell DSL package auto-imported
- `mode: Script` — top-level statements allowed (no `fn main` required)
- `interpreter: true` — run via interpreter, not codegen
- Task syntax (`task`, `depends_on:`, `phony`) enabled by shell compiler mode

See `doc/design/simple_shell_design.md` for full `.ssh` DSL design.

## Structured Export: EasyFix Integration

The `structured_export_placement` lint rule should use the **existing EasyFix infrastructure** rather than creating a new fix mechanism.

### Lint Rule as EasyFix

```simple
# In src/app/fix/rules.spl (add to existing 9 rules)

fn check_structured_export_placement(source: text, file: text) -> List<EasyFix>:
    """Rule L:structured_export_placement - must be at top of __init__.spl"""
    val fixes = []

    # Only applies to __init__.spl files
    if not file.ends_with("__init__.spl"):
        return fixes

    val export_line = None
    val first_code_line = None

    for_each_line(source) \ctx:
        if ctx.trimmed.starts_with("structured_export:"):
            export_line = Some(ctx.line)
        elif not ctx.trimmed.starts_with("mod ") and not ctx.trimmed.starts_with("pub mod ") and not ctx.trimmed.starts_with("#") and ctx.trimmed.? and first_code_line.is_none():
            first_code_line = Some(ctx.line)

    # If structured_export appears after other code, suggest moving it
    if export_line.? and first_code_line.? and export_line > first_code_line:
        # Extract the structured_export block and move it
        fixes.push(EasyFix(
            id: "L:structured_export_placement",
            description: "Move structured_export to top of __init__.spl",
            replacements: [
                # Remove from current position, insert after mod declarations
            ],
            confidence: FixConfidence.Safe,
        ))

    fixes
```

### Auto-Conversion as EasyFix

```simple
# Rule L:flat_export_to_structured - convert repetitive export use to structured_export

fn check_flat_export_to_structured(source: text, file: text) -> List<EasyFix>:
    """Suggest structured_export when 10+ export use with shared prefixes"""
    val fixes = []

    if not file.ends_with("__init__.spl"):
        return fixes

    # Count export use statements grouped by prefix
    val prefix_counts = {}
    for_each_line(source) \ctx:
        if ctx.trimmed.starts_with("export use "):
            val path = ctx.trimmed.strip_prefix("export use ")
            val prefix = path.split(".").first ?? ""
            prefix_counts[prefix] = (prefix_counts[prefix] ?? 0) + 1

    # If any prefix has 3+ exports, suggest structured_export
    for prefix, count in prefix_counts:
        if count >= 3:
            fixes.push(EasyFix(
                id: "L:flat_export_to_structured",
                description: "Convert repeated export use {prefix}.* to structured_export",
                replacements: [
                    # Build structured_export block from flat exports
                ],
                confidence: FixConfidence.Likely,
            ))
            break  # One fix per file

    fixes
```

### Integration with Existing Fix Pipeline

These rules plug into the existing `src/app/fix/main.spl` pipeline:

```bash
# Preview
simple fix __init__.spl --dry-run

# Auto-fix
simple fix __init__.spl --fix-all

# Interactive
simple fix __init__.spl --fix-interactive
```

The existing `FixApplicator` handles:
- Byte-offset replacement (sorted end-to-start)
- Overlap detection
- Confidence-based filtering (`Safe` auto-applies, `Likely` prompts)

No new fix infrastructure needed.

## Project-Level Extension Config

Projects can override or extend the registry in `simple.sdn`:

```sdn
extensions:
    .ssh:
        default_imports: [std.shell.*, myproject.shell_helpers.*]
        lint_profile: shell_strict

    .spl:
        # Add project-wide default imports
        additional_imports: [myproject.prelude.*]
```

## Implementation Files

- `rust/compiler/src/project.rs` — add `ExtensionConfig` lookup during file loading
- `rust/compiler/src/module_resolver/` — use registry for prelude/default import resolution
- `rust/lib/std/src/prelude.spl` — existing prelude (unchanged, referenced by registry)
- `src/app/fix/rules.spl` — add `L:structured_export_placement` and `L:flat_export_to_structured` rules
- `src/app/fix/main.spl` — existing fix pipeline (unchanged, new rules plug in)

## Backward Compatibility

Fully backward compatible:
- Existing `.spl` and `.sdn` behavior unchanged
- Registry formalizes what is already convention-based
- New extensions (`.ssh`) register cleanly
- Project-level overrides are optional

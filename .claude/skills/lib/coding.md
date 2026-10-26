# Coding Skill - Workflow & Standards

Reference: See `ref_coding` memory for syntax rules, type names, lambda shorthands, EasyFix rules.

## Compile & Fix Workflow

```bash
bin/simple build                    # Debug build
bin/simple build --release          # Release build
bin/simple lint <changed .spl files> # Simple source lint — fix all denies before committing
sh scripts/check/lint-cached.shs <changed .spl files>  # same lint, 0.03s on unchanged files
# ^ lint costs ~11.7s startup + ~3.3-4.0s PER FUNCTION (~119s for a 120-line file).
#   Lint one file at a time: batching is superlinear (2 files >600s vs 119s for 1).
#   Caches clean verdicts only — findings and edits always re-lint.
#   See doc/07_guide/tooling/build_fast_path.md
bin/simple fix file.spl --dry-run   # Preview auto-fixes
bin/simple fix file.spl             # Apply fixes
bin/simple lint file.spl --fix      # Lint with auto-fix
```

## Coding Standards

- Only make directly requested changes
- Don't add features beyond what's asked
- Don't refactor surrounding code or add docstrings to unchanged code
- Don't add error handling for impossible scenarios
- Delete unused code completely (no `_vars`, `// removed`)
- Prefer 3 similar lines over premature abstraction

## Test Documentation (CRITICAL)

Use docstring markdown in SPipe tests — NO `println()` for documentation:

```simple
describe "Feature":
    """# Feature — Tests NFA pattern matching."""

    it "matches single chars":
        """Given: Pattern("a"), When: matches("a"), Then: true"""
        expect(Pattern.new("a").matches("a")).to_equal(true)
```

## Scripts Policy

ALL scripts in Simple (.spl), NOT Python/Bash. Run: `bin/simple scripts/tool.spl args`

## See Also

- `doc/07_guide/language/style/coding_style.md` — Full style guide
- `doc/07_guide/quick_reference/syntax_quick_reference.md` — Syntax reference

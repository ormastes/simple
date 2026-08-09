---
alwaysApply: false
---
# Quick Commands Reference

```bash
# Build
bin/simple build                    # Debug build (runs bootstrap by default)
bin/simple build bootstrap          # 3-stage self-compilation verification

# Quality
bin/simple lint <changed .spl files> # Pure-Simple source linter
bin/simple build fmt                # Rust formatter
bin/simple build check              # Rust clippy + rustfmt check + Rust tests

# Documentation Coverage
bin/simple stats                    # Doc coverage in stats
bin/simple doc-coverage             # Terminal coverage report
bin/simple doc-coverage --missing   # Show undocumented items

# Tools
bin/simple fix file.spl --dry-run   # Preview fixes
bin/simple todo-scan                # Update TODO tracking
bin/simple bug-add --id=X           # Add bug
bin/simple bug-gen                  # Generate bug report
```

## Fast Path (measured 2026-08-09)

```bash
# Cached lint — 152.00s cold -> 0.03s warm. Caches CLEAN verdicts only;
# findings and edited files always re-lint. Verdict line is last on stdout.
sh scripts/check/lint-cached.shs src/lib/common/base_encoding.spl
SIMPLE_LINT_CACHE=0 sh scripts/check/lint-cached.shs <files>   # bypass

# ALWAYS record binary identity with any timing — the symlink target is
# replaced by other agents mid-session (3 distinct builds seen in one session).
readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"

# Provenance probe: bin/simple is currently the RUST SEED, and says so.
bin/simple --version 2>&1 | head -2

# grep here is a wrapped ugrep honouring .gitignore (measured 4 hits vs 17).
/usr/bin/grep -rn "pattern" src/       # exhaustive scans / censuses
```

- `bin/simple lint` costs ~11.7s startup + ~3.3-4.0s **per function decl**,
  superlinear. A 120-line file takes ~119s. **Do not batch files** — 2 files
  exceeded 600s vs 119s for 1.
- No pure-Simple binary can lint: `bootstrap/stage3/simple lint` is
  `unknown command` (exit 1). `simple test` GREEN does not prove self-hosted.
- Detail: `doc/07_guide/tooling/build_fast_path.md`

## Setup
```bash
scripts/setup/setup.shs          # Create bin/simple symlink (auto-detects platform)
sh config/mcp/install.shs # Install MCP config
```

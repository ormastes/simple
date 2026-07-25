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

## Setup
```bash
scripts/setup/setup.shs          # Create bin/simple symlink (auto-detects platform)
sh config/mcp/install.shs # Install MCP config
```

---
alwaysApply: false
---
# Quick Commands Reference

```bash
# Build
bin/simple build                    # Debug build
bin/simple build --release          # Release build

# Quality
bin/simple build lint               # Linter
bin/simple build fmt                # Formatter
bin/simple build check              # All checks
bin/simple build --warn-docs        # Documentation coverage

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
scripts/setup.sh          # Create bin/simple symlink (auto-detects platform)
sh config/mcp/install.shs # Install MCP config
```

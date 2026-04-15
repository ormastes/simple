---
paths:
  - "**"
alwaysApply: false
---
# Version Control

- Use **jj** (Jujutsu) as primary VCS, colocated with git
- **NEVER create branches** - work directly on `main`
- Commit: `jj commit -m "message"` (auto-tracks all changes, no staging needed)
- Push: `jj bookmark set main -r @- && jj git push --bookmark main`
- Fetch: `jj git fetch && jj rebase -d main@origin`

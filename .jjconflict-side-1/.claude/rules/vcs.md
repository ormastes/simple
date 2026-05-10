---
paths:
  - "**"
alwaysApply: false
---
# Version Control

- Use **jj** (Jujutsu) as primary VCS, colocated with git
- **NEVER create branches** - work directly on `main`
- Commit: `jj commit -m "message"` (auto-tracks all changes, no staging needed)
- Push: `sj bookmark set main -r @- && sj git push --bookmark main`
- Fetch: `sj raw jj git fetch && sj raw jj rebase -d main@origin`

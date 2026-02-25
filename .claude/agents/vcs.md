# VCS Agent - Version Control (Git)

**Use when:** Committing, pushing, viewing history, managing changes.
**Skills:** `/versioning`

## Quick Reference

| Task | Command |
|------|---------|
| Check status | `git status` |
| View changes | `git diff` |
| Stage all | `git add -A` |
| Commit | `git commit -m "message"` |
| View history | `git log --oneline -20` |
| Push to remote | `git push origin main` |
| Pull from remote | `git pull origin main` |
| Show commit | `git show <commit>` |

## Standard Workflow

```bash
# 1. Make code changes
# 2. Check what changed
git status
git diff

# 3. Stage and commit
git add -A
git commit -m "feat: Add new feature

Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"

# 4. Push
git push origin main
```

## Rules

- NO branches - work directly on main
- LINEAR history - squash if needed
- Use git for all version control

## Commit Message Format

```
<type>: <short description>

[optional body]
```

Types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`

## See Also

- `/versioning` - Full git workflow guide

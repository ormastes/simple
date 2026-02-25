# Versioning Skill - Git Workflow

## Important Rules

1. **NO BRANCHES** - Work directly on `main`, do not create feature branches
2. **Use git** for all version control operations
3. **LINEAR HISTORY** - Keep history linear, squash if needed before push

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
| Show change details | `git show <commit>` |
| Amend last commit | `git commit --amend` |
| View staged | `git diff --cached` |

## Standard Workflow

### Making Changes (Work on Main)
```bash
# 1. Make your code changes
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

### Fixing Past Commits
```bash
# Amend last commit (only if not pushed)
git add -A
git commit --amend -m "updated message"

# Or create a new fix commit
git add -A
git commit -m "fix: correct previous change"
```

## Commit Message Format

```
<type>: <short description>

[optional body]

[optional footer]
```

Types: `feat`, `fix`, `refactor`, `docs`, `test`, `chore`, `perf`

# Bitbucket Setup Skill

Interactive setup for Bitbucket Cloud REST 2.0 integration via `bin/simple itf bb`.
App Passwords are deprecated as of 2026 — this skill walks the user through
creating a **Repository Access Token** (Bearer auth).

## Prerequisites Check

1. Repo origin is on `bitbucket.org` (`git remote -v` shows `bitbucket.org`)
2. User is workspace or repo admin (required to mint Repository Access Tokens)
3. `bin/simple` is built and `bin/simple itf` is on PATH

If origin is not Bitbucket, abort and route to `gh_setup` instead.

## Procedure

### Step 1 — Mint a Repository Access Token

Repository Access Tokens are scoped to a single repo and use HTTP Bearer auth.
Direct the user to the Bitbucket Cloud docs:
`https://support.atlassian.com/bitbucket-cloud/docs/repository-access-tokens/`

In the Bitbucket UI:
1. Navigate to: **Repository → Repository settings → Access tokens** (under Security)
2. Click **Create Repository Access Token**
3. Give it a name (e.g. `simple-itf-bot`)
4. Select scopes:
   - `pullrequest:write` (create PRs, comment, approve, merge)
   - `repository`        (read commit statuses)
5. Click **Create**, then copy the token (it is shown once)

Note: Repository Access Tokens cannot be configured as a "user with merge
access" in branch restriction rules. If your branch policy enforces required
reviewers, the bot must be added as an explicit reviewer when opening the PR.

### Step 2 — Save the Token

Edit `~/.config/itf/auth.sdn` and add:

```
bitbucket:
    token: "<paste-token-here>"
```

File mode must be `0600`. Verify:

```bash
chmod 600 ~/.config/itf/auth.sdn
ls -la ~/.config/itf/auth.sdn
```

### Step 3 — Set Workspace and Repo Defaults

Set environment variables in your shell rc file (or pass per-invocation flags):

```bash
export BB_WORKSPACE=<your-workspace-slug>
export BB_REPO=<your-repo-slug>
```

Or pass `--workspace` and `--repo` to every `itf bb` invocation.

### Step 4 — Verify

Pick any open PR and view it:

```bash
bin/simple itf bb pr view <PR_ID>
```

Expected: PR title, state, source/dest branch printed. If you see
`blocked-auth: unauthorized (HTTP 401)`, the token is wrong or revoked.

## Verification Checklist

- [ ] `~/.config/itf/auth.sdn` has a `bitbucket:` section with `token:`
- [ ] File mode is `0600`
- [ ] `BB_WORKSPACE` and `BB_REPO` set (or `--workspace`/`--repo` planned per invocation)
- [ ] `bin/simple itf bb pr view <ID>` succeeds on a known PR
- [ ] Token has `pullrequest:write` + `repository` scopes

## Error Handling

| Error                              | Cause / Fix                                   |
|------------------------------------|-----------------------------------------------|
| `blocked-auth: unauthorized (401)` | Token wrong, expired, or revoked. Re-mint.    |
| `blocked-auth: forbidden (403)`    | Token lacks scope. Add `pullrequest:write`.   |
| `not found (404)`                  | Wrong workspace/repo slug or PR id.           |
| `--workspace and --repo required`  | Set `BB_WORKSPACE`/`BB_REPO` or pass flags.   |

## Integration

- **With `bb_push`**: `bb_push` requires this setup to have completed.
- **With `repo_and_pull_req --target=bb`**: orchestrator dispatches here when
  origin is bitbucket.org.

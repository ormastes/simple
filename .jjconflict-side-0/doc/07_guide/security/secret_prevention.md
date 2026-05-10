# Secret Prevention Guide

Hardcoded secrets (API keys, tokens, private keys, passwords) in source code
are one of the most common security vulnerabilities. Once committed to git,
secrets persist in the repository history even after deletion. This guide
covers how the Simple toolchain prevents accidental secret commits.

---

## Why Secret Prevention Matters

- **Git history is permanent.** Even if you delete a secret in a later commit,
  it remains in `git log` and can be extracted by anyone with repo access.
- **Public repos are scanned.** Bots continuously scan GitHub for leaked AWS
  keys, API tokens, and other credentials. Leaked keys are exploited within
  minutes.
- **Supply chain risk.** A leaked signing key or registry token can allow
  attackers to publish malicious packages under your name.
- **Compliance.** PCI-DSS, SOC2, and HIPAA all require that secrets never
  appear in source code.

---

## Setting Up the Pre-Commit Hook

### Automatic (recommended)

The `scripts/setup.sh` script installs the secret scanner as a git pre-commit
hook:

```sh
scripts/setup.sh
```

### Manual

```sh
cp scripts/secret-scan.shs .git/hooks/pre-commit
chmod +x .git/hooks/pre-commit
```

### Testing the Hook

Stage a file with a fake secret and try to commit:

```sh
echo 'val key = "AKIAIOSFODNN7EXAMPLE"' > /tmp/test_secret.spl
cp /tmp/test_secret.spl .
git add test_secret.spl
git commit -m "test"
# Should be blocked by the hook
rm test_secret.spl
git reset HEAD test_secret.spl
```

---

## Secret Patterns Detected

### Critical (blocks commit)

| Pattern | Example | Description |
|---------|---------|-------------|
| AWS Access Key | `AKIA...` (20 chars) | AWS IAM access key ID |
| GitHub Token | `ghp_...`, `gho_...`, `ghs_...`, `ghr_...` | GitHub personal/OAuth/app/refresh tokens |
| Anthropic Key | `sk-ant-...` | Anthropic API key |
| OpenAI Key | `sk-...` (20+ chars) | OpenAI API key |
| Google API Key | `AIza...` (39 chars) | Google Cloud/Maps API key |
| Private Key | `-----BEGIN ... PRIVATE KEY-----` | PEM-encoded private key |
| Slack Token | `xoxb-...`, `xoxp-...`, `xoxs-...` | Slack bot/user/session tokens |
| Stripe Key | `sk_live_...`, `pk_live_...` | Stripe live API keys |

### Warning (flagged, not blocked in CI)

| Pattern | Description |
|---------|-------------|
| Connection strings | `://user:password@host` patterns |
| Database passwords | `password=...` in config |
| High-entropy hex | Hex strings > 64 characters (possible keys) |
| High-entropy base64 | Base64-like strings > 40 characters |
| JWT tokens | Three base64url segments separated by dots |

---

## Handling False Positives

### Inline Annotation

Add `@allow(hardcoded_secret)` above the line:

```simple
# @allow(hardcoded_secret)
val EXPECTED_HASH = "e3b0c44298fc1c149afbf4c8996fb924..."
```

### .secretscanignore File

Create a `.secretscanignore` file in the repo root. List file paths
(one per line) that should be excluded from scanning:

```
# Test fixtures with fake credentials
test/fixtures/fake_credentials.sdn
test/fixtures/mock_tokens.spl

# Documentation examples
doc/07_guide/security/secret_prevention.md
```

### Test Files

Test files (`*_spec.spl`, `*_test.spl`) are automatically excluded from
the high-entropy string checks (hex > 64 chars, base64 > 40 chars) to
reduce noise from test fixtures. Specific token patterns (AWS, GitHub, etc.)
are still checked in test files.

---

## Credential Storage Best Practices

### Environment Variables (CI/CD)

```sh
export SIMPLE_TOKEN="ghp_..."
export AWS_ACCESS_KEY_ID="AKIA..."
bin/simple publish my_package
```

### Credentials File (~/.simple/credentials.sdn)

```sdn
# ~/.simple/credentials.sdn
# Created by 'simple login'
registry:
  token: ghp_...
  type: github_pat
```

This file is:
- Created by `simple login`
- Located outside the repository
- Automatically read by `simple publish` and `simple install`
- Already in `.gitignore` (`credentials.sdn`)

### Package Signing Keys

```sh
# Generate a signing key pair
simple key generate

# Keys are stored at:
#   ~/.simple/signing_key.pem   (private, chmod 600)
#   ~/.simple/signing_key.pub   (public, shareable)
```

Never commit `signing_key.pem`. The `.gitignore` already excludes `*.pem`.

---

## CI/CD Secret Injection

### GitHub Actions

```yaml
env:
  SIMPLE_TOKEN: ${{ secrets.SIMPLE_TOKEN }}

steps:
  - run: bin/simple publish my_package
```

### GitLab CI

```yaml
variables:
  SIMPLE_TOKEN: $SIMPLE_TOKEN  # Set in CI/CD Settings > Variables

script:
  - bin/simple publish my_package
```

### Generic CI

Set `SIMPLE_TOKEN` as a masked environment variable in your CI system.
The Simple CLI reads it automatically (see `src/app/package.registry/auth.spl`).

---

## What To Do If You Accidentally Commit a Secret

### Immediate Steps

1. **Rotate the secret immediately.** Generate a new key/token and invalidate
   the old one. Do this BEFORE anything else.

2. **Remove from the current branch:**
   ```sh
   # Edit the file to remove the secret
   jj commit -m "remove leaked secret"
   ```

3. **Check for damage.** Review access logs for the compromised credential.
   For AWS, check CloudTrail. For GitHub, check the audit log.

### History Cleanup (optional)

Even after removing the secret from HEAD, it remains in git history.
For public repositories, you MUST rotate the secret regardless. History
cleanup is optional but recommended:

```sh
# Use git-filter-repo (preferred) or BFG Repo Cleaner
git filter-repo --invert-paths --path path/to/file_with_secret
```

**Warning:** History rewriting is a destructive operation that forces all
collaborators to re-clone. Only do this for truly sensitive leaks.

### Reporting

If a Simple registry signing key or token is compromised:
1. Revoke the key: `simple trust revoke <fingerprint>`
2. Report to the Simple security team
3. Re-sign all affected packages with a new key

---

## Simple-Native Scanner

The Simple-native scanner (`src/app/tools/secret_scan.spl`) integrates
with `simple lint --secrets` for in-editor and CI scanning:

```sh
# Scan entire project
bin/simple lint --secrets

# Scan specific directory
bin/simple lint --secrets src/

# JSON output for CI
bin/simple lint --secrets --format=json
```

The native scanner detects all patterns listed above plus JWT tokens and
database passwords in connection strings. It respects `@allow(hardcoded_secret)`
annotations and `.secretscanignore`.

# GitHub Deploy Setup Guide

Step-by-step guide to set up the Simple package registry infrastructure on GitHub.

---

## Prerequisites

- GitHub organization: `simple-lang` (or your own org)
- GitHub account with admin access
- `oras` CLI installed locally

---

## 1. Create the Registry Index Repository

```bash
# Create the repo
gh repo create simple-lang/registry --public --description "Simple package registry index"

# Clone and set up structure
git clone https://github.com/simple-lang/registry.git
cd registry

# Create index directory structure
mkdir -p index
echo "# Simple Package Registry Index" > README.md

# Create empty listing
cat > index/_listing.sdn << 'EOF'
# Package listing for search
# Auto-updated by publish workflows

packages |name, description, latest_version|
EOF

git add .
git commit -m "Initial registry structure"
git push
```

## 2. Configure GHCR Access

### Enable GitHub Packages

1. Go to **Organization Settings** > **Packages**
2. Ensure "GitHub Packages" is enabled
3. Set default visibility to **Public** for new packages

### Create a Personal Access Token (PAT)

1. Go to **Settings** > **Developer settings** > **Personal access tokens** > **Tokens (classic)**
2. Create a new token with scopes:
   - `read:packages`
   - `write:packages`
   - `repo` (for index PRs)
3. Save the token securely

### Configure Local Credentials

```bash
# Option 1: Environment variable (recommended for CI)
export SIMPLE_TOKEN=ghp_your_token_here

# Option 2: Credentials file (for local development)
mkdir -p ~/.simple
cat > ~/.simple/credentials.sdn << EOF
registry:
  token: ghp_your_token_here
  type: github_pat
EOF
chmod 600 ~/.simple/credentials.sdn
```

## 3. Set Up GitHub Actions Secrets

For each package repository that will publish:

1. Go to **Repository Settings** > **Secrets and variables** > **Actions**
2. Add secret `REGISTRY_TOKEN` with a PAT that has `repo` scope on the registry repo

## 4. Add Publish Workflow to Package Repos

Copy `.github/workflows/publish.yml` from the Simple compiler repo to your package repository.

## 5. Test the Setup

### Verify oras authentication

```bash
oras login ghcr.io --username YOUR_USERNAME --password $SIMPLE_TOKEN
```

### Publish a test package

```bash
# Create a test package
mkdir test-pkg && cd test-pkg
simple init test-pkg

# Publish
simple publish --dry-run    # Preview
simple publish              # Actually publish
```

### Install from registry

```bash
simple install test-pkg
```

## 6. Maintenance

### Clear local cache

```bash
rm -rf ~/.simple/cache/registry
```

### Prune old versions from GHCR

Use the GitHub UI or API to delete old package versions if needed.

### Monitor Actions usage

GitHub free tier: 2000 minutes/month for Actions. Monitor at **Organization Settings** > **Billing** > **Actions**.

---

## Troubleshooting

| Issue | Solution |
|-------|----------|
| `oras: command not found` | Install oras CLI (see publish command help) |
| `401 Unauthorized` | Check token scopes and expiration |
| `403 Forbidden` | Ensure packages are public, check org settings |
| `Package not found` | Verify OCI reference format: `ghcr.io/simple-lang/name:version` |
| `Index fetch failed` | Check internet connection, try `simple install --clear-cache` |

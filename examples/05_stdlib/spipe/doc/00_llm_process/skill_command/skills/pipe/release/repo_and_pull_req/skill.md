<!-- llm-process-gen: managed source=pipe_release_repo_and_pull_req_skill source_sha256=b0d8ff77e62a1f146b0cb5f61c09a80186698ae2321053ec11daaaa8f3ce8c45 content_sha256=b0d8ff77e62a1f146b0cb5f61c09a80186698ae2321053ec11daaaa8f3ce8c45 -->
---
name: repo_and_pull_req
description: GitHub and Jira/Confluence integration — setup, push, wiki, and autonomous PR review. Routes to sub-skills in git/ and jira/ directories.
---

# Repo & Pull Request Skill — Dispatcher

Unified skill for GitHub and Jira/Confluence operations: setup, push, wiki, and PR review.

## Usage

## Normalized contract clauses

- One isolated release session owns one work branch and one non-main worktree.
- `release/version.sdn` is the sole version authority and all other version locations are checked projections.
- Beta maintenance admits only caller-selected reviewed bug-fix commits with exact provenance and renewed result-revision evidence.
- Bootstrap periodically performs read-only main-to-release convergence discovery and never selects or cherry-picks fixes automatically.
- An approved release-first emergency fix requires an exact reviewed forward-port receipt to main.
- Main remains the independent development trunk and never tracks or becomes a release branch.
- Protected refs change only through exact-revision compare-and-swap integration authority.
- Each changed source policy support or toolchain identity creates a new immutable candidate attempt.
- Build and qualify the exact candidate once and reject required failures or fallback artifacts.
- Promotion reuses admitted artifacts without rebuilding and pushes exactly one signed annotated tag.
- Release admission requires focused failures to reach zero followed by one clean whole-suite confirmation.
- Withdrawal preserves published tags assets and history and corrections use a new version.
- Protected PR self review uses a required status check because GitHub forbids an author APPROVED review and never claims provider approval.
- Ordinary code and text are eligible by default absent an operator deny or constrain record with code, text, file, directory_files, and directory_recursive scopes.
- Push, retarget, base, diff, ruleset, policy, or expiry invalidation requires a fresh exact-head review and a new self-review admission dispatch.
- Rejection remediation follows the exact reason without broadening protected integration, candidate, release, signing, or publication authority.

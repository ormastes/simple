# LLM Dashboard Web Login Guide

Operator notes for the `llm_dashboard` web login and Peer Base Pack (PBP) bootstrap flow.

---

## Purpose

The web login surface gives operators a bounded administrative entrypoint into the dashboard UI. The PBP flow uses a bootstrap admin credential so the first operator can sign in before a longer-lived user-management flow exists.

This guide is operational, not architectural. For the broader assistant/dashboard design see:

- [Application Architecture](../architecture/application_architecture.md)
- [KAIROS-Like Simple MCP + LLM Dashboard Architecture](../../04_architecture/kairos_like_simple_mcp_llm_dashboard.md)

## Required Environment Variables

Set these before starting the web-facing `llm_dashboard` process:

```bash
export SIMPLE_LLM_DASHBOARD_ADMIN_USER='admin'
export SIMPLE_LLM_DASHBOARD_ADMIN_PASSWORD='change-this-before-exposing-web-ui'
```

Operator rules:

- `SIMPLE_LLM_DASHBOARD_ADMIN_USER` defines the bootstrap administrator username accepted by the login form.
- `SIMPLE_LLM_DASHBOARD_ADMIN_PASSWORD` defines the bootstrap administrator password.
- Do not commit either value to repo-tracked files.
- Do not leave the password empty when the web UI is reachable by other users or hosts.

## Bootstrap Credential Behavior

The bootstrap credential exists to get the first operator into the dashboard without a separate provisioning step.

Expected behavior:

- The configured bootstrap admin credential is accepted by the login form.
- The bootstrap credential is environment-driven, so rotating it means changing the environment and restarting the dashboard process.
- The bootstrap credential is an operator bootstrap path, not a durable shared team password.
- If the environment variables are absent, operators should treat web login as not provisioned and configure them before exposing the login page.

Operational recommendation:

- Use a unique password per environment.
- Rotate the bootstrap password after initial bring-up or any suspected disclosure.
- Prefer secret-injection from your supervisor, container runtime, or system service manager over shell history or checked-in config.

## Session Storage

The web login flow stores auth state under:

```text
.build/llm_dashboard/auth
```

Treat that directory as runtime state, not source.

Expected contents:

- login/session records for authenticated browser sessions
- auth-related transient state needed by the dashboard web process

Operator rules:

- Keep `.build/llm_dashboard/auth` writable by the dashboard process.
- Do not share the directory across unrelated environments unless you intentionally want shared auth state.
- Deleting the directory invalidates active web sessions and forces re-login.
- Preserve normal file permissions; session material should not be world-readable.

## PBP Bring-Up Checklist

1. Set `SIMPLE_LLM_DASHBOARD_ADMIN_USER`.
2. Set `SIMPLE_LLM_DASHBOARD_ADMIN_PASSWORD`.
3. Ensure `.build/llm_dashboard/auth` exists or can be created by the process user.
4. Start the web-facing dashboard.
5. Sign in once with the bootstrap admin credential.
6. Verify that a session record appears under `.build/llm_dashboard/auth`.

## Troubleshooting

If login fails:

- verify both environment variables are set in the same process environment that launches `llm_dashboard`
- check that `.build/llm_dashboard/auth` is writable
- restart after rotating bootstrap credentials so the new values are loaded

If sessions appear to reset unexpectedly:

- check for cleanup jobs removing `.build/llm_dashboard/auth`
- check whether the process is running under a different working directory or ephemeral workspace
- check whether multiple environments are reusing the same browser against different dashboard instances

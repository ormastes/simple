# llm_caret env-gated system specs have no honest BLOCKED outcome (2026-11-12)

Status: open. Severity: P2 (suite signal, not a product defect).

## Repro (Windows host, phase-1 seed, release/1.0.0)

```
bin/simple.exe test test/03_system/app/llm_caret/feature/<spec>_spec.spl --no-session-daemon --timeout 600
bin/simple.exe test test/03_system/app/llm_caret/infra_servers_system_spec.spl --no-session-daemon --timeout 600
```

| spec | verdict | first failure |
|---|---|---|
| smux_capability_socket | ERROR 1/1 failed | `precondition: mandatory absolute SMUX_SOCKET_TEST_CONFIG` |
| smux_configured_binding_socket | ERROR 1/1 failed | `precondition: mandatory absolute SMUX_SOCKET_TEST_CONFIG` |
| smux_owned_terminal_transport | ERROR 1/1 failed | `precondition: mandatory absolute SMUX_OWNED_TEST_CONFIG` |
| smux_runtime_control_socket | ERROR 1/1 failed | fixture config precondition |
| smux_signed_binding_socket | ERROR 1/1 failed | fixture config precondition |
| smux_runtime_terminal_transport | ERROR 1/1 failed | `precondition: absolute shell and sleep helpers are required` (`/bin/sh`, `/bin/sleep`) |
| infra_servers_system | OK, executed=4 skipped=4 | `pending("BLOCKED: no local SMTP/IMAP/minio/FTP/Confluence ...")` |

## Root cause

1. The six smux specs are `AUTHORED_UNRUN` POSIX/Linux acceptance specs. They
   need a strict SDN fixture config (`test/helpers/smux_owned_process_fixture.spl`
   `owned_fixture_config_for`): a delegated cgroup path, broker/helper programs
   with digests, and `/usr/bin/stat` and `/usr/bin/id`. **No script in the repo
   provisions that config**, so these specs cannot pass on any host, Linux
   included, until an operator builds the fixture by hand. On Windows they are
   unsupported by construction.
2. `infra_servers_system_spec` gates on live external servers. That gate is
   legitimate, but `pending()` is tallied as `skipped`, and the file reports
   `outcome=OK`. All-skipped therefore looks like a pass.
3. The test runner's outcome set is frozen
   (`OK/ERROR/CRASHED/TERMINATED/TIMEOUT/NOT_RUN`,
   `src/app/test_runner_new/test_runner_single.spl:39`). It has no
   `BLOCKED`/`UNSUPPORTED` class, so an environment-gated spec must either
   fail (the smux specs, honest but noisy) or skip (infra, which looks vacuous).
   `@tag:in-development` does not fit, because it is for unimplemented behaviour,
   not a missing environment.

## Needed (owner decision)

- Add a counted `outcome=BLOCKED reason=<...>` verdict class. It must never count
  as passed and must stay visible in the summary. Map `pending("BLOCKED: ...")` and
  `Err("precondition: ...")` onto it.
- Add a fixture provisioner (`.shs`) that writes the `SMUX_*_TEST_CONFIG` SDN on a
  Linux host with cgroup v2 delegation. Without it the smux specs are permanently red.
- Native evidence: run the smux specs on Linux with a provisioned fixture.

No skip was added and no spec was weakened.

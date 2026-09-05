# Lane: llm_caret_mail_hardening (2026-08-25)

Three production gaps in the LLM Caret mail tools (infra_mail.spl), from
doc/00_llm_process/feature_expert/llm_caret_messaging/skill.md.

## Gap 1 — STARTTLS (SMTP 587 / IMAP 143)
- runtime_need: wrap an EXISTING connected TCP fd in a TLS client session
  (in-place upgrade after `STARTTLS`/`220` or tagged OK).
- facade_checked: src/lib/nogc_sync_mut/io/tls_sffi.spl (all externs),
  src/runtime/runtime.h rt_tls_* (lines 388–396),
  src/runtime/runtime_https_openssl_core.c (SSL_set_fd only INSIDE
  rt_tls_client_connect, line 363 — not exported per-fd),
  src/compiler_rust/runtime/src/value/net_tls.rs (no from-fd entry).
  Verdict: NO backing extern exists anywhere.
- chosen_path: keep the honest pre-connect refusal; implement the full
  STARTTLS negotiation as a transport-free pure-Simple state machine
  (src/app/llm_caret/infra_mail_starttls.spl) proven against scripted
  transcripts (test/01_unit/app/llm_caret/infra_mail_starttls_spec.spl);
  file the runtime need as
  doc/08_tracking/bug/tls_no_fd_upgrade_blocks_starttls_2026-08-25.md
  (proposed extern: rt_tls_client_from_fd).
- rejected_shortcuts:
  - inventing an unbacked `rt_tls_client_from_fd` extern (silently returns
    nil; forbidden by the unbacked-extern ratchet in .claude/rules/vcs.md);
  - reconnecting on 993/465 behind the operator's back when 587/143 is
    configured (silent config rewrite);
  - a live third wrapper row exercising STARTTLS upgrade: BLOCKED — even
    though greenmail 2.x can offer STARTTLS, no runtime symbol can wrap the
    live fd, so the row cannot pass on any server. Unblock condition: the
    runtime lane lands rt_tls_client_from_fd (see bug doc), then wire
    starttls_begin/feed into infra_mail after 220 / tagged OK and add the row.

## Gap 2 — RFC 3501 FETCH parsing
- Literal-aware framer + typed FETCH parser added to the owner module
  src/lib/nogc_sync_mut/imap/parse.spl (imap_response_complete,
  imap_parse_fetch_response, item/header accessors); UID FETCH builder in
  imap/build.spl (imap_build_uid_fetch); infra_mail mail_list/mail_read now
  parse via them. Sabotage verified: disabling literal skipping turns
  fetch_parse_spec red (9→8 pass), restore → green.
- Known upstream quirk (recorded, not fixed here): imap/types.spl
  imap_next_tag never advances tag_seq (struct-by-value); infra_mail keeps
  its own monotonic tag counter.

## Gap 3 — bounded reads
- runtime_need: per-call TLS read deadline. facade_checked: runtime.h
  rt_tls_client_read_timeout EXISTS (C runtime_https_openssl_core.c:562,
  Rust net_tls.rs:351, interpreter_extern/mod.rs:2537) and positive-probed
  on the deployed binary (probe returned empty text, not unknown-extern).
- chosen_path: add-smallest-owner-facade — tls_read_timeout in tls_sffi.spl;
  TCP path reuses existing tcp_fd_set_read_timeout. infra_mail bounds every
  reply read with a monotonic deadline; error text
  "mail server timed out after N ms". Spec: infra_mail_timeout_spec.spl
  (silent in-process listener, 2 s budget, wall < 5 s asserted).
- rejected_shortcuts: raw rt_* extern declared in the spec (facade rule);
  nonblocking+poll loop (no poll facade needed — timeout externs suffice).

## Verification (2026-08-25, seed binary 60641352 bytes 05:16)
- fetch_parse_spec 9/9; infra_mail_starttls_spec 8/8; infra_mail_timeout_spec
  3/3; infra_tools_spec 17/17; parse_multibyte 9/9; smtp_spec 62/62;
  send_email_validate_multibyte 6/6; send_mime_shadow 5/5;
  response_code_numeric_guard 1/1; gc_async_mut/smtp/types_spec 5/5.
- Live wrapper: baseline PASS (2 live rows) before the change; after the
  change PASS — 2 live rows, 0 failed. Mid-lane a concurrent session added a
  BLOCKED wiki row to infra_servers_system_spec (2 permanently-blocked rows),
  so classify_log was generalized: live rows = passed - skipped must be
  exactly the 2 gated rows; blocked-row drift in either direction stays FAIL
  (selftest grew 10→12 fixtures).
- Evidence-level note: the TLS read-deadline branch (tls_read_timeout on
  993/465) is PROBE-verified only (extern backed in C+Rust+interpreter and
  positive-probed on the deployed binary); the timeout spec and the live
  wrapper both exercise plaintext ports. A TLS server fixture was out of
  scope ("no live TLS server required").
- Lint: environment-BLOCKED, not passed — the 2026-08-25 seed redeploy fails
  to parse src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl (an
  untouched file fails identically; filed as
  doc/08_tracking/bug/seed_redeploy_breaks_test_runner_accessor_rewrite_parse_2026-08-25.md).
  Substitute syntax evidence: every changed module compiles in the spec runs.
- Untracked stale .smf siblings of edited modules (imap/*, smtp/*, io/tcp,
  io/tls_sffi) quarantined to the session scratchpad.

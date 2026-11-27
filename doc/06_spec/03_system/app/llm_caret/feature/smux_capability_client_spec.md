# Hosted smux capability response classification

Source: `test/03_system/app/llm_caret/feature/smux_capability_client_spec.spl`.
Status: **AUTHORED_UNRUN**. Companion authored; execution and docgen not run.

The existing hosted smux `--request` branch now classifies the exact
`runtime-binding-capabilities-v1` command using a bounded strict SDN decoder.
A valid discovery response can produce CLI exit zero while both advertised
binding and framed CoreMux capabilities remain false. This does not prove
runtime binding, attachment, execution authorization or readiness.

1. Feed the actual authenticated server-dispatch response into the production
   client classifier. Check all seven typed fields and both false flags.
2. Reject actual unauthorized and unsupported bind responses. Bind refusal
   remains a failure even if an unrelated legacy-success body is supplied.
3. Reject wrong versions, types, kinds, scopes, transports and reasons.
4. Reject uninstalled positive capabilities and wrongly typed false booleans.
5. Reject duplicate, missing or extra fields and trailing authored tokens.
   Enforce the 4096-byte cap using a multibyte UTF-8 oversized response.
6. Restrict structured discovery success to the exact operation. Preserve the
   generic legacy predicate unchanged; unrelated SDN never becomes success.

This is source-import dispatch/classifier integration, not socket or compiled
CLI acceptance. The separate authored actual compiled/socket scenario is
`test/03_system/app/llm_caret/feature/smux_capability_socket_spec.spl`; its manual
records private publication, real CLI exit classifications and retained group
cleanup. It remains AUTHORED_UNRUN, blocked pending admitted artifacts,
delegated resources and a root-authorized test slot. No fake executable or
stream substitutes for that evidence.

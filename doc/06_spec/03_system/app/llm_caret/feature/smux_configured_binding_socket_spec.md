# Real configured smux negative binding and vacant target

Status: **AUTHORED_UNRUN**. No compiler, socket, host, broker or provider runtime was executed to qualify this source.

Source: `test/03_system/app/llm_caret/feature/smux_configured_binding_socket_spec.spl`.
Shared support: `test/helpers/smux_capability_socket_fixture.spl` and `test/helpers/smux_owned_process_fixture.spl`.

Mandatory inputs:

- `SMUX_SOCKET_TEST_CONFIG`: the existing exact nine-field protected fixture config: root, brokerProgram, brokerDigest, smuxProgram, smuxDigest, delegatedCgroupPath, memoryLimitBytes, snapshotDigest, cacheIdentity. Explicit compiled regular no-follow binaries and matching observed digests are required. Broker root must be fresh, private mode 0700, owned by the current UID and disjoint from the enrolled host root.
- `SMUX_CONFIGURED_HOST_ROOT`: an absolute pre-provisioned protected enrolled HostLocalRoot, mode 0700/current UID, with the actual fixed `smux-runtime-policy.sdn`, enrollment, policy, authority state, and available exclusive host journal lock. This scenario does not synthesize enrollment, grant, workload or parent-budget evidence.
- Actual native grouped stream backend, broker delegation and memory enforcement; `/usr/bin/stat` and `/usr/bin/id` fixture oracles; C/POSIX locale for their textual output. Missing inputs or capabilities fail preconditions, never skip or pass.

Steps:

1. Start the real compiled `--serve-runtime-owner-file OWNER HOSTROOT` under the retained broker. Create and validate the private mode-0600 owner file, fresh nonce/token and actual loopback endpoint within the existing bounded publication deadline. Publication is discovery only.
2. Observe real configured planning-only discovery and authenticate every runtime route. A separate compiled `--request` process must return strict V2 planning facts, while wrong-token discovery, create, plan, prepare, bind, inspect and target operations return unauthorized.
3. Create a real vacant target without a shell and replay the exact named target. The authenticated `create-runtime-target-v3 NAME` uses existing smux metadata creation. Repeated name and exact target lookup must preserve generated IDs, incarnation, revision and vacancy. No fabricated pane is installed.
4. Reject unplanned binding and malformed planning without acquiring helper authority. The valid wire request contains deliberately unretained negative-case operation/budget references. Binding must fail before helper begin because no exact retained plan exists. Strict refusal facts claim no commit, stream, cleanup owner or host charge; repeating the same UID preserves refusal and exact target fences.
5. Stop through the authenticated compiled client. Drain only the fixture server stdout to explicit EOF, then require actual group terminal proof and canonical cleanup. This is fixture cleanup, not host reservation release or Container attachment.

Every post-start operation returns the fixture carrier before assertions. The scenario retains that carrier globally after start, exercise and stop, including cleanup-bearing failure. Startup without a valid endpoint uses the existing bounded broker cancellation/proof path, never a raw PID fallback. Request timeouts remain uncertain and do not trigger fresh operation IDs.

Positive binding still requires real canonical plan publication, cryptographically signed matching helper packets staged through the agreed same-owner preparation route, actual runtime output through the sole pane reader, and verified host settlement. This negative scenario neither substitutes synthetic positive capability evidence nor includes a failing placeholder for that separate acceptance requirement.

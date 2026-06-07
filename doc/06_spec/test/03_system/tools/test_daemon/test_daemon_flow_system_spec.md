# test_daemon_flow_system_spec

> @cover src/app/test_daemon/daemon.spl 80%

<!-- sdn-diagram:id=test_daemon_flow_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_flow_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_flow_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_flow_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_flow_system_spec

@cover src/app/test_daemon/daemon.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-SYS-031 to #TDMN-SYS-040 |
| Category | Infrastructure / System Test |
| Status | Active |
| Source | `test/03_system/tools/test_daemon/test_daemon_flow_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/app/test_daemon/daemon.spl 80%
@cover src/app/test_daemon/client.spl 80%
Test Daemon End-to-End Flow System Test

Tests the complete request flow: submit → daemon reads → process →
respond → client reads. Verifies the full IPC cycle works with
real filesystem operations.

## Scenarios

### TestDaemon Flow

### single request lifecycle

#### completes full submit-process-respond cycle

1. flow setup
2. client write lock
   - Expected: flow_req_count() equals `1`
   - Expected: reqs.len() equals `1`
   - Expected: reqs[0][0] equals `req_id`
   - Expected: reqs[0][2] equals `test/flow_spec.spl`
3. daemon process and respond
4. daemon cleanup requests
   - Expected: flow_req_count() equals `0`
   - Expected: flow_resp_count() equals `1`
   - Expected: client_check_response(req_id) is true
   - Expected: resp[0] equals `2`
   - Expected: resp[1] equals `test/flow_spec.spl`
   - Expected: resp[2] equals `Tests completed`
5. flow cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
flow_setup()
client_write_lock()
# 1. Client submits
val req_id = client_submit_request(1, "test/flow_spec.spl")
expect(flow_req_count()).to_equal(1)
# 2. Daemon reads
val reqs = daemon_read_requests()
expect(reqs.len()).to_equal(1)
expect(reqs[0][0]).to_equal(req_id)
expect(reqs[0][2]).to_equal("test/flow_spec.spl")
# 3. Daemon processes and responds
daemon_process_and_respond(req_id, "test/flow_spec.spl", 10, 0)
daemon_cleanup_requests()
expect(flow_req_count()).to_equal(0)
expect(flow_resp_count()).to_equal(1)
# 4. Client reads response
expect(client_check_response(req_id)).to_equal(true)
val resp = client_read_response(req_id)
expect(resp[0]).to_equal(2)
expect(resp[1]).to_equal("test/flow_spec.spl")
expect(resp[2]).to_equal("Tests completed")
flow_cleanup()
```

</details>

### batch processing

#### processes 3 requests in one poll cycle

1. flow setup
2. client write lock
   - Expected: reqs.len() equals `3`
3. flow process all requests
4. daemon cleanup requests
   - Expected: client_check_response(id1) is true
   - Expected: client_check_response(id2) is true
   - Expected: client_check_response(id3) is true
5. flow cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
flow_setup()
client_write_lock()
val id1 = client_submit_request(1, "test/a_spec.spl")
val id2 = client_submit_request(1, "test/b_spec.spl")
val id3 = client_submit_request(1, "test/c_spec.spl")
# Daemon reads all
val reqs = daemon_read_requests()
expect(reqs.len()).to_equal(3)
# Daemon processes all
flow_process_all_requests(reqs)
daemon_cleanup_requests()
# All clients get responses
expect(client_check_response(id1)).to_equal(true)
expect(client_check_response(id2)).to_equal(true)
expect(client_check_response(id3)).to_equal(true)
flow_cleanup()
```

</details>

### multi-cycle processing

#### processes requests across multiple poll cycles

1. flow setup
2. client write lock
3. daemon process and respond
4. daemon cleanup requests
5. daemon process and respond
6. daemon cleanup requests
   - Expected: r1[0] equals `2`
   - Expected: r2[0] equals `2`
7. flow cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
flow_setup()
client_write_lock()
# Cycle 1
val id1 = client_submit_request(1, "test/cycle1_spec.spl")
val reqs1 = daemon_read_requests()
daemon_process_and_respond(reqs1[0][0], reqs1[0][2], 3, 0)
daemon_cleanup_requests()
# Cycle 2
val id2 = client_submit_request(1, "test/cycle2_spec.spl")
val reqs2 = daemon_read_requests()
daemon_process_and_respond(reqs2[0][0], reqs2[0][2], 7, 1)
daemon_cleanup_requests()
# Both responses exist
val r1 = client_read_response(id1)
val r2 = client_read_response(id2)
expect(r1[0]).to_equal(2)
expect(r2[0]).to_equal(2)
flow_cleanup()
```

</details>

### error handling

#### client gets empty for missing response

1. flow setup
   - Expected: resp[0] equals `-1`
   - Expected: resp[1] equals ``
2. flow cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
flow_setup()
val resp = client_read_response("nonexistent_id")
expect(resp[0]).to_equal(-1)
expect(resp[1]).to_equal("")
flow_cleanup()
```

</details>

#### daemon handles empty request directory

1. flow setup
   - Expected: reqs.len() equals `0`
2. flow cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
flow_setup()
val reqs = daemon_read_requests()
expect(reqs.len()).to_equal(0)
flow_cleanup()
```

</details>

### isolation

#### requests and responses use separate directories

1. flow setup
   - Expected: flow_req_count() equals `1`
   - Expected: flow_resp_count() equals `0`
2. daemon process and respond
   - Expected: flow_resp_count() equals `1`
3. flow cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
flow_setup()
val id = client_submit_request(1, "test/iso_spec.spl")
expect(flow_req_count()).to_equal(1)
expect(flow_resp_count()).to_equal(0)
daemon_process_and_respond(id, "test/iso_spec.spl", 1, 0)
expect(flow_resp_count()).to_equal(1)
flow_cleanup()
```

</details>

### concurrent agents flow

#### 5 agents submit, daemon batch processes, all get results

1. flow setup
2. client write lock
   - Expected: flow_req_count() equals `5`
   - Expected: reqs.len() equals `5`
3. flow process reqs with offset
4. daemon cleanup requests
5. flow verify all responses
6. flow cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
flow_setup()
client_write_lock()
# 5 agents submit concurrently
val agent_ids = flow_submit_n_agents(5)
expect(flow_req_count()).to_equal(5)
# Daemon reads all
val reqs = daemon_read_requests()
expect(reqs.len()).to_equal(5)
# Daemon processes all
flow_process_reqs_with_offset(reqs)
daemon_cleanup_requests()
# All 5 agents get responses
flow_verify_all_responses(agent_ids, 5)
flow_cleanup()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

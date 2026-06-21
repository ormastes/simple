# test_daemon_concurrent_spec

> @cover src/app/test_daemon/daemon.spl 80%

<!-- sdn-diagram:id=test_daemon_concurrent_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_daemon_concurrent_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_daemon_concurrent_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_daemon_concurrent_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_daemon_concurrent_spec

@cover src/app/test_daemon/daemon.spl 80%

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TDMN-SYS-001 to #TDMN-SYS-020 |
| Category | Infrastructure / System Test |
| Status | Active |
| Source | `test/03_system/tools/test_daemon/test_daemon_concurrent_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

@cover src/app/test_daemon/daemon.spl 80%
@cover src/app/test_daemon/client.spl 80%
Test Daemon Concurrent System Test

Tests concurrent request submission and deduplication via real
file-based IPC. Simulates multiple "agents" writing requests
to the same directory and verifies correct handling.

## Scenarios

### TestDaemon Concurrent IPC

### multi-agent submission

#### handles requests from 5 concurrent agents

- conc setup
- agent submit
- agent submit
- agent submit
- agent submit
- agent submit
   - Expected: count_req_files() equals `5`
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
agent_submit(1, "test/a_spec.spl", 1)
agent_submit(2, "test/b_spec.spl", 1)
agent_submit(3, "test/c_spec.spl", 1)
agent_submit(4, "test/d_spec.spl", 1)
agent_submit(5, "test/e_spec.spl", 1)
expect(count_req_files()).to_equal(5)
conc_cleanup()
```

</details>

#### preserves all request data

- conc setup
   - Expected: reqs.len() equals `2`
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id1 = agent_submit(10, "test/foo_spec.spl", 1)
val id2 = agent_submit(20, "test/bar_spec.spl", 3)
val reqs = read_all_requests()
expect(reqs.len()).to_equal(2)
conc_cleanup()
```

</details>

#### handles 20 rapid sequential submissions

- conc setup
- submit n rapid agents
   - Expected: count_req_files() equals `20`
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
submit_n_rapid_agents(20)
expect(count_req_files()).to_equal(20)
conc_cleanup()
```

</details>

### deduplication simulation

#### allows same test from different agents

- conc setup
   - Expected: count_req_files() equals `2`
   - Expected: id1 != id2 is true
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id1 = agent_submit(1, "test/shared_spec.spl", 1)
val id2 = agent_submit(2, "test/shared_spec.spl", 1)
# Both should create separate request files (dedup happens in daemon)
expect(count_req_files()).to_equal(2)
expect(id1 != id2).to_equal(true)
conc_cleanup()
```

</details>

#### daemon responds to first, redirects second

- conc setup
- daemon respond
- daemon respond
   - Expected: resp1[0] equals `2`
   - Expected: resp2[0] equals `2`
   - Expected: resp1[2] equals `5`
   - Expected: resp2[2] equals `5`
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id1 = agent_submit(1, "test/dedup_spec.spl", 1)
val id2 = agent_submit(2, "test/dedup_spec.spl", 1)
# Daemon runs test once, responds to both
daemon_respond(id1, 2, "test/dedup_spec.spl", 5, 0)
daemon_respond(id2, 2, "test/dedup_spec.spl", 5, 0)
val resp1 = read_response(id1)
val resp2 = read_response(id2)
expect(resp1[0]).to_equal(2)
expect(resp2[0]).to_equal(2)
expect(resp1[2]).to_equal(5)
expect(resp2[2]).to_equal(5)
conc_cleanup()
```

</details>

### cache simulation

#### returns cached response for unchanged test

- conc setup
- daemon respond cached
   - Expected: resp[0] equals `6`
   - Expected: resp[2] equals `10`
   - Expected: resp[4] is true
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id = agent_submit(1, "test/cached_spec.spl", 1)
daemon_respond_cached(id, "test/cached_spec.spl", 10)
val resp = read_response(id)
expect(resp[0]).to_equal(6)
expect(resp[2]).to_equal(10)
expect(resp[4]).to_equal(true)
conc_cleanup()
```

</details>

#### executes and caches new test

- conc setup
- daemon respond
   - Expected: resp[0] equals `2`
   - Expected: resp[4] is false
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id = agent_submit(1, "test/new_spec.spl", 1)
daemon_respond(id, 2, "test/new_spec.spl", 8, 0)
val resp = read_response(id)
expect(resp[0]).to_equal(2)
expect(resp[4]).to_equal(false)
conc_cleanup()
```

</details>

### clean run bypass

#### always executes clean run (kind=3)

- conc setup
- daemon respond
   - Expected: resp[0] equals `2`
   - Expected: resp[4] is false
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id = agent_submit(1, "test/force_spec.spl", 3)
daemon_respond(id, 2, "test/force_spec.spl", 7, 0)
val resp = read_response(id)
expect(resp[0]).to_equal(2)
expect(resp[4]).to_equal(false)
conc_cleanup()
```

</details>

### mixed request types

#### handles RUN_SINGLE, CLEAN, and STATUS simultaneously

- conc setup
   - Expected: count_req_files() equals `3`
   - Expected: reqs.len() equals `3`
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id1 = agent_submit(1, "test/a_spec.spl", 1)
val id2 = agent_submit(2, "test/b_spec.spl", 3)
val id3 = agent_submit(3, "", 4)
expect(count_req_files()).to_equal(3)
val reqs = read_all_requests()
# All three requests present
expect(reqs.len()).to_equal(3)
conc_cleanup()
```

</details>

### response delivery

#### each agent gets its own response

- conc setup
- daemon respond
- daemon respond
- daemon respond
   - Expected: r1[0] equals `2`
   - Expected: r1[2] equals `10`
   - Expected: r2[0] equals `3`
   - Expected: r2[3] equals `2`
   - Expected: r3[0] equals `2`
   - Expected: r3[2] equals `7`
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id1 = agent_submit(1, "test/a_spec.spl", 1)
val id2 = agent_submit(2, "test/b_spec.spl", 1)
val id3 = agent_submit(3, "test/c_spec.spl", 1)
daemon_respond(id1, 2, "test/a_spec.spl", 10, 0)
daemon_respond(id2, 3, "test/b_spec.spl", 3, 2)
daemon_respond(id3, 2, "test/c_spec.spl", 7, 0)
val r1 = read_response(id1)
val r2 = read_response(id2)
val r3 = read_response(id3)
expect(r1[0]).to_equal(2)
expect(r1[2]).to_equal(10)
expect(r2[0]).to_equal(3)
expect(r2[3]).to_equal(2)
expect(r3[0]).to_equal(2)
expect(r3[2]).to_equal(7)
conc_cleanup()
```

</details>

#### response arrives after request cleanup

- conc setup
   - Expected: reqs.len() equals `1`
- delete req files in dir
   - Expected: count_req_files() equals `0`
- daemon respond
   - Expected: resp[0] equals `2`
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val id = agent_submit(1, "test/x_spec.spl", 1)
# Daemon reads and processes request
val reqs = read_all_requests()
expect(reqs.len()).to_equal(1)
# Daemon deletes request files after processing
delete_req_files_in_dir()
expect(count_req_files()).to_equal(0)
# Daemon writes response
daemon_respond(id, 2, "test/x_spec.spl", 5, 0)
# Agent can still read response
val resp = read_response(id)
expect(resp[0]).to_equal(2)
conc_cleanup()
```

</details>

### stress test

#### handles 50 agents submitting different tests

- conc setup
   - Expected: count_req_files() equals `50`
- respond n agents stress
   - Expected: count_resp_files() equals `50`
- verify n agents stress
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val ids = submit_n_agents_stress(50, "test/stress_")
expect(count_req_files()).to_equal(50)
# Daemon processes all and writes responses
respond_n_agents_stress(ids, 50, "test/stress_")
expect(count_resp_files()).to_equal(50)
# All agents get correct responses
verify_n_agents_stress(ids, 50)
conc_cleanup()
```

</details>

#### handles 10 agents all requesting same test

- conc setup
   - Expected: count_req_files() equals `10`
- respond n agents same test
- verify n agents same test
- conc cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
conc_setup()
val ids = submit_n_agents_same_test(10, "test/same_spec.spl")
expect(count_req_files()).to_equal(10)
# Daemon deduplicates — responds to all with same result
respond_n_agents_same_test(ids, 10, "test/same_spec.spl", 15)
# All agents get response
verify_n_agents_same_test(ids, 10, 15)
conc_cleanup()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

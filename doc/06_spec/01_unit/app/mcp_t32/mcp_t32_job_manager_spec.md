# Mcp T32 Job Manager Specification

> <details>

<!-- sdn-diagram:id=mcp_t32_job_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_job_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_job_manager_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_job_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 60 | 60 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Job Manager Specification

## Scenarios

### T32 Job Lifecycle

#### job creation

#### creates job with valid id

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val job = make_job("job_1", "session_a", "t32_cmm_run")
expect(job.job_id).to_equal("job_1")
expect(job.session_id).to_equal("session_a")
expect(job.tool_name).to_equal("t32_cmm_run")
```

</details>

#### starts in queued status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val job = make_job("job_2", "session_a", "t32_cmd_run")
expect(job.status).to_equal("queued")
```

</details>

#### valid transitions

#### transitions queued to running

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val job = make_job("job_3", "s1", "t32_cmm_run")
val running = try_transition(job, "running")
expect(running.status).to_equal("running")
```

</details>

#### transitions running to completed

1. var job = make job
2. job = try transition
   - Expected: done.status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_4", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val done = try_transition(job, "completed")
expect(done.status).to_equal("completed")
```

</details>

#### transitions running to failed with error message

1. var job = make job
2. job = try transition
   - Expected: failed.status equals `failed`
   - Expected: failed.error_message equals `PRACTICE script error at line 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_5", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val failed = try_transition_with_error(job, "failed", "PRACTICE script error at line 42")
expect(failed.status).to_equal("failed")
expect(failed.error_message).to_equal("PRACTICE script error at line 42")
```

</details>

#### transitions running to timed_out

1. var job = make job
2. job = try transition
   - Expected: timed.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_6", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val timed = try_transition(job, "timed_out")
expect(timed.status).to_equal("timed_out")
```

</details>

#### transitions running to cancelled

1. var job = make job
2. job = try transition
   - Expected: cancelled.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_7", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val cancelled = try_transition(job, "cancelled")
expect(cancelled.status).to_equal("cancelled")
```

</details>

#### transitions running to waiting_target

1. var job = make job
2. job = try transition
   - Expected: waiting.status equals `waiting_target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_8", "s1", "t32_cmd_run")
job = try_transition(job, "running")
val waiting = try_transition(job, "waiting_target")
expect(waiting.status).to_equal("waiting_target")
```

</details>

#### transitions waiting_target back to running

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: resumed.status equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_9", "s1", "t32_cmd_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_target")
val resumed = try_transition(job, "running")
expect(resumed.status).to_equal("running")
```

</details>

#### transitions running to waiting_practice

1. var job = make job
2. job = try transition
   - Expected: waiting.status equals `waiting_practice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_10", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val waiting = try_transition(job, "waiting_practice")
expect(waiting.status).to_equal("waiting_practice")
```

</details>

#### invalid transitions

#### rejects completed to running

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: invalid.status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_11", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "completed")
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("completed")
```

</details>

#### rejects failed to running

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: invalid.status equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_12", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "failed")
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("failed")
```

</details>

#### rejects timed_out to running

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: invalid.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_13", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "timed_out")
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("timed_out")
```

</details>

#### rejects cancelled to running

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: invalid.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_14", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "cancelled")
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("cancelled")
```

</details>

#### rejects queued to completed directly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val job = make_job("job_15", "s1", "t32_cmm_run")
val invalid = try_transition(job, "completed")
expect(invalid.status).to_equal("queued")
```

</details>

#### allows queued to cancelled

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val job = make_job("job_16", "s1", "t32_cmm_run")
val cancelled = try_transition(job, "cancelled")
expect(cancelled.status).to_equal("cancelled")
```

</details>

### T32 Job Manager Operations

#### job creation via manager

#### creates job and increments counter

1. var mgr = make manager
   - Expected: result1[0] equals `job_1`
   - Expected: result1[1] equals `ok`
   - Expected: result2[0] equals `job_2`
   - Expected: result2[1] equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val result1 = manager_create_job(mgr, "s1", "t32_cmm_run", false)
expect(result1[0]).to_equal("job_1")
expect(result1[1]).to_equal("ok")
val result2 = manager_create_job(mgr, "s1", "t32_cmd_run", false)
expect(result2[0]).to_equal("job_2")
expect(result2[1]).to_equal("ok")
```

</details>

#### assigns unique ids across sessions

1. var mgr = make manager
   - Expected: r1[0] == r2[0] is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val r1 = manager_create_job(mgr, "s1", "t32_cmm_run", false)
val r2 = manager_create_job(mgr, "s2", "t32_cmm_run", false)
expect(r1[0] == r2[0]).to_equal(false)
```

</details>

#### listing jobs

#### lists all active jobs

1. var mgr = make manager
2. manager create job
3. manager create job
4. manager create job
   - Expected: active.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
manager_create_job(mgr, "s1", "t32_cmd_run", false)
manager_create_job(mgr, "s2", "t32_eval", false)
val active = manager_list_jobs(mgr)
expect(active.len()).to_equal(3)
```

</details>

#### filters jobs by session_id

1. var mgr = make manager
2. manager create job
3. manager create job
4. manager create job
   - Expected: s1_jobs.len() equals `2`
   - Expected: s1_jobs[0].session_id equals `s1`
   - Expected: s1_jobs[1].session_id equals `s1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
manager_create_job(mgr, "s2", "t32_cmd_run", false)
manager_create_job(mgr, "s1", "t32_eval", false)
val s1_jobs = manager_list_jobs_by_session(mgr, "s1")
expect(s1_jobs.len()).to_equal(2)
expect(s1_jobs[0].session_id).to_equal("s1")
expect(s1_jobs[1].session_id).to_equal("s1")
```

</details>

#### excludes terminal jobs from active list

1. var mgr = make manager
2. manager create job
3. manager create job
4. mgr jobs[1] = try transition
5. mgr jobs[1] = try transition
   - Expected: active.len() equals `1`
   - Expected: active[0].job_id equals `job_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
manager_create_job(mgr, "s1", "t32_cmd_run", false)
# Transition second job to completed
mgr.jobs[1] = try_transition(mgr.jobs[1], "running")
mgr.jobs[1] = try_transition(mgr.jobs[1], "completed")
val active = manager_list_jobs(mgr)
expect(active.len()).to_equal(1)
expect(active[0].job_id).to_equal("job_1")
```

</details>

#### getting jobs

#### returns correct job by id

1. var mgr = make manager
2. manager create job
3. manager create job
   - Expected: job.job_id equals `job_2`
   - Expected: job.session_id equals `s2`
   - Expected: job.tool_name equals `t32_cmd_run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
manager_create_job(mgr, "s2", "t32_cmd_run", false)
val job = manager_get_job(mgr, "job_2")
expect(job.job_id).to_equal("job_2")
expect(job.session_id).to_equal("s2")
expect(job.tool_name).to_equal("t32_cmd_run")
```

</details>

#### returns not_found sentinel for nonexistent id

1. var mgr = make manager
   - Expected: job.job_id equals ``
   - Expected: job.status equals `not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val job = manager_get_job(mgr, "job_999")
expect(job.job_id).to_equal("")
expect(job.status).to_equal("not_found")
```

</details>

#### cancelling jobs

#### cancels a queued job

1. var mgr = make manager
2. manager create job
   - Expected: ok is true
   - Expected: job.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
val ok = manager_cancel_job(mgr, "job_1")
expect(ok).to_equal(true)
val job = manager_get_job(mgr, "job_1")
expect(job.status).to_equal("cancelled")
```

</details>

#### cancels a running job

1. var mgr = make manager
2. manager create job
3. mgr jobs[0] = try transition
   - Expected: ok is true
   - Expected: job.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
mgr.jobs[0] = try_transition(mgr.jobs[0], "running")
val ok = manager_cancel_job(mgr, "job_1")
expect(ok).to_equal(true)
val job = manager_get_job(mgr, "job_1")
expect(job.status).to_equal("cancelled")
```

</details>

#### rejects cancel on completed job

1. var mgr = make manager with completed job
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager_with_completed_job()
val ok = manager_cancel_job(mgr, "job_1")
expect(ok).to_equal(false)
```

</details>

#### concurrent limit

#### enforces max 16 concurrent jobs

1. var mgr = make manager
   - Expected: r[1] equals `ok`
   - Expected: overflow[0] equals ``
   - Expected: overflow[1] equals `error:max_concurrent_exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
var i = 0
while i < 16:
    val r = manager_create_job(mgr, "s1", "t32_cmm_run", false)
    expect(r[1]).to_equal("ok")
    i = i + 1
val overflow = manager_create_job(mgr, "s1", "t32_cmm_run", false)
expect(overflow[0]).to_equal("")
expect(overflow[1]).to_equal("error:max_concurrent_exceeded")
```

</details>

#### allows new jobs after terminal transitions free slots

1. var mgr = make manager with 16 jobs first completed
   - Expected: r[1] equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager_with_16_jobs_first_completed()
val r = manager_create_job(mgr, "s1", "t32_cmm_run", false)
expect(r[1]).to_equal("ok")
```

</details>

#### cleanup

#### removes expired terminal jobs

1. var mgr = make manager with expired completed job
   - Expected: removed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager_with_expired_completed_job()
val removed = manager_cleanup(mgr, 400000)
expect(removed).to_equal(1)
```

</details>

#### preserves active jobs during cleanup

1. var mgr = make manager
2. manager create job
   - Expected: removed equals `0`
   - Expected: mgr.jobs.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
# Job stays queued (active)
val removed = manager_cleanup(mgr, 999999)
expect(removed).to_equal(0)
expect(mgr.jobs.len()).to_equal(1)
```

</details>

### T32 Background Execution Model

#### background flag

#### background true returns immediately with job_id

1. var mgr = make manager
   - Expected: result[0] equals `job_1`
   - Expected: result[1] equals `ok`
   - Expected: job.background is true
   - Expected: job.status equals `queued`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val result = manager_create_job(mgr, "s1", "t32_cmm_run", true)
expect(result[0]).to_equal("job_1")
expect(result[1]).to_equal("ok")
val job = manager_get_job(mgr, "job_1")
expect(job.background).to_equal(true)
expect(job.status).to_equal("queued")
```

</details>

#### foreground job also gets job_id for timeout continuation

1. var mgr = make manager
   - Expected: result[0] equals `job_1`
   - Expected: job.background is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
val result = manager_create_job(mgr, "s1", "t32_cmm_run", false)
expect(result[0]).to_equal("job_1")
val job = manager_get_job(mgr, "job_1")
expect(job.background).to_equal(false)
```

</details>

#### polling

#### poll returns pending for queued job

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val job = make_job("job_1", "s1", "t32_cmm_run")
expect(poll_status(job)).to_equal("pending")
```

</details>

#### poll returns pending for running job

1. var job = make job
2. job = try transition
   - Expected: poll_status(job) equals `pending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
expect(poll_status(job)).to_equal("pending")
```

</details>

#### poll returns completed for finished job

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: poll_status(job) equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "completed")
expect(poll_status(job)).to_equal("completed")
```

</details>

#### poll returns failed for error job

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: poll_status(job) equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "failed")
expect(poll_status(job)).to_equal("failed")
```

</details>

#### result availability

#### result available after completion

1. var job = make job
2. job = try transition
3. job = set result
4. job = try transition
   - Expected: result_available(job) is true
   - Expected: job.result_text equals `Flash programming complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = set_result(job, "Flash programming complete")
job = try_transition(job, "completed")
expect(result_available(job)).to_equal(true)
expect(job.result_text).to_equal("Flash programming complete")
```

</details>

#### result not available while running

1. var job = make job
2. job = try transition
   - Expected: result_available(job) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
expect(result_available(job)).to_equal(false)
```

</details>

#### result available after failure with error

1. var job = make job
2. job = try transition
3. job = try transition with error
   - Expected: result_available(job) is true
   - Expected: job.error_message equals `connection lost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition_with_error(job, "failed", "connection lost")
expect(result_available(job)).to_equal(true)
expect(job.error_message).to_equal("connection lost")
```

</details>

#### resource URI

#### produces correct resource URI format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = job_resource_uri("job_42")
expect(uri).to_equal("t32://jobs/job_42")
```

</details>

#### URI starts with t32 scheme

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = job_resource_uri("job_1")
expect(uri).to_start_with("t32://")
```

</details>

#### URI contains jobs path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = job_resource_uri("job_123")
expect(uri).to_contain("/jobs/")
```

</details>

### T32 Job Timeout Policy

#### default timeouts per tool type

#### cmm_run has 60s default timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_timeout_for_tool("t32_cmm_run")).to_equal(60000)
```

</details>

#### cmd_run has 10s default timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_timeout_for_tool("t32_cmd_run")).to_equal(10000)
```

</details>

#### eval has 3s default timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_timeout_for_tool("t32_eval")).to_equal(3000)
```

</details>

#### window_capture has 5s default timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_timeout_for_tool("t32_window_capture")).to_equal(5000)
```

</details>

#### screenshot has 10s default timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_timeout_for_tool("t32_screenshot")).to_equal(10000)
```

</details>

#### flash_program has 120s default timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_timeout_for_tool("t32_flash_program")).to_equal(120000)
```

</details>

#### unknown tool gets default 10s timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(default_timeout_for_tool("t32_unknown")).to_equal(10000)
```

</details>

#### custom timeout override

#### custom timeout_ms overrides default

1. var job = make job
   - Expected: custom_job.timeout_ms equals `30000`
   - Expected: default_timeout_for_tool("t32_cmm_run") equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
# Simulate custom timeout
val custom_job = T32Job(
    job_id: job.job_id,
    session_id: job.session_id,
    tool_name: job.tool_name,
    status: job.status,
    error_message: job.error_message,
    result_text: job.result_text,
    created_at_ms: job.created_at_ms,
    timeout_ms: 30000,
    background: job.background
)
expect(custom_job.timeout_ms).to_equal(30000)
# Verify default would have been different
expect(default_timeout_for_tool("t32_cmm_run")).to_equal(60000)
```

</details>

#### timeout behavior

#### timed out status set correctly on timeout

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: job.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "timed_out")
expect(job.status).to_equal("timed_out")
```

</details>

#### timeout does not affect background job flag

1. var job = make bg job
2. job = try transition
3. job = try transition
   - Expected: job.status equals `timed_out`
   - Expected: job.background is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_bg_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "timed_out")
expect(job.status).to_equal("timed_out")
expect(job.background).to_equal(true)
```

</details>

#### timed_out is a terminal state

1. var job = make job
2. job = try transition
3. job = try transition
   - Expected: invalid.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "timed_out")
# Cannot transition out of timed_out
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("timed_out")
```

</details>

### T32 Job Manager Edge Cases

#### state machine completeness

#### waiting_practice can complete directly

1. var job = make job
2. job = try transition
3. job = try transition
4. job = try transition
   - Expected: job.status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_practice")
job = try_transition(job, "completed")
expect(job.status).to_equal("completed")
```

</details>

#### waiting_practice can fail

1. var job = make job
2. job = try transition
3. job = try transition
4. job = try transition with error
   - Expected: job.status equals `failed`
   - Expected: job.error_message equals `PRACTICE error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_practice")
job = try_transition_with_error(job, "failed", "PRACTICE error")
expect(job.status).to_equal("failed")
expect(job.error_message).to_equal("PRACTICE error")
```

</details>

#### waiting_target can time out

1. var job = make job
2. job = try transition
3. job = try transition
4. job = try transition
   - Expected: job.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmd_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_target")
job = try_transition(job, "timed_out")
expect(job.status).to_equal("timed_out")
```

</details>

#### waiting_target can be cancelled

1. var job = make job
2. job = try transition
3. job = try transition
4. job = try transition
   - Expected: job.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmd_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_target")
job = try_transition(job, "cancelled")
expect(job.status).to_equal("cancelled")
```

</details>

#### manager with mixed sessions

#### handles multiple sessions independently

1. var mgr = make manager
2. manager create job
3. manager create job
4. manager create job
   - Expected: a_jobs.len() equals `2`
   - Expected: b_jobs.len() equals `1`
   - Expected: a_jobs[0].tool_name equals `t32_cmm_run`
   - Expected: a_jobs[1].tool_name equals `t32_eval`
   - Expected: b_jobs[0].tool_name equals `t32_cmd_run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mgr = make_manager()
manager_create_job(mgr, "session_a", "t32_cmm_run", true)
manager_create_job(mgr, "session_b", "t32_cmd_run", false)
manager_create_job(mgr, "session_a", "t32_eval", false)
val a_jobs = manager_list_jobs_by_session(mgr, "session_a")
val b_jobs = manager_list_jobs_by_session(mgr, "session_b")
expect(a_jobs.len()).to_equal(2)
expect(b_jobs.len()).to_equal(1)
expect(a_jobs[0].tool_name).to_equal("t32_cmm_run")
expect(a_jobs[1].tool_name).to_equal("t32_eval")
expect(b_jobs[0].tool_name).to_equal("t32_cmd_run")
```

</details>

#### job result lifecycle

#### result persists through completion

1. var job = make job
2. job = try transition
3. job = set result
4. job = try transition
   - Expected: job.result_text equals `DO flash_program.cmm completed successfully`
   - Expected: job.status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = set_result(job, "DO flash_program.cmm completed successfully")
job = try_transition(job, "completed")
expect(job.result_text).to_equal("DO flash_program.cmm completed successfully")
expect(job.status).to_equal("completed")
```

</details>

#### error message persists on failure

1. var job = make job
2. job = try transition
3. job = try transition with error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition_with_error(job, "failed", "T4101: Command timed out after 60000ms")
expect(job.error_message).to_start_with("T4101")
expect(job.error_message).to_contain("60000ms")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_job_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 Job Lifecycle
- T32 Job Manager Operations
- T32 Background Execution Model
- T32 Job Timeout Policy
- T32 Job Manager Edge Cases

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 60 |
| Active scenarios | 60 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

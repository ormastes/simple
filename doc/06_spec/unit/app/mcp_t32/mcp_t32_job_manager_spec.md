# Mcp T32 Job Manager Specification

> Tests covering T32 Job Lifecycle, T32 Job Manager Operations, T32 Background Execution Model, T32 Job Timeout Policy, T32 Job Manager Edge Cases.

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

- creates job with valid id
   - Expected: job.job_id equals `job_1`
   - Expected: job.session_id equals `session_a`
   - Expected: job.tool_name equals `t32_cmm_run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates job with valid id")
val job = make_job("job_1", "session_a", "t32_cmm_run")
expect(job.job_id).to_equal("job_1")
expect(job.session_id).to_equal("session_a")
expect(job.tool_name).to_equal("t32_cmm_run")
```

</details>

#### starts in queued status

- starts in queued status
   - Expected: job.status equals `queued`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts in queued status")
val job = make_job("job_2", "session_a", "t32_cmd_run")
expect(job.status).to_equal("queued")
```

</details>

#### valid transitions

#### transitions queued to running

- transitions queued to running
   - Expected: running.status equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions queued to running")
val job = make_job("job_3", "s1", "t32_cmm_run")
val running = try_transition(job, "running")
expect(running.status).to_equal("running")
```

</details>

#### transitions running to completed

- transitions running to completed
   - Expected: done.status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions running to completed")
var job = make_job("job_4", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val done = try_transition(job, "completed")
expect(done.status).to_equal("completed")
```

</details>

#### transitions running to failed with error message

- transitions running to failed with error message
   - Expected: failed.status equals `failed`
   - Expected: failed.error_message equals `PRACTICE script error at line 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions running to failed with error message")
var job = make_job("job_5", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val failed = try_transition_with_error(job, "failed", "PRACTICE script error at line 42")
expect(failed.status).to_equal("failed")
expect(failed.error_message).to_equal("PRACTICE script error at line 42")
```

</details>

#### transitions running to timed_out

- transitions running to timed_out
   - Expected: timed.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions running to timed_out")
var job = make_job("job_6", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val timed = try_transition(job, "timed_out")
expect(timed.status).to_equal("timed_out")
```

</details>

#### transitions running to cancelled

- transitions running to cancelled
   - Expected: cancelled.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions running to cancelled")
var job = make_job("job_7", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val cancelled = try_transition(job, "cancelled")
expect(cancelled.status).to_equal("cancelled")
```

</details>

#### transitions running to waiting_target

- transitions running to waiting_target
   - Expected: waiting.status equals `waiting_target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions running to waiting_target")
var job = make_job("job_8", "s1", "t32_cmd_run")
job = try_transition(job, "running")
val waiting = try_transition(job, "waiting_target")
expect(waiting.status).to_equal("waiting_target")
```

</details>

#### transitions waiting_target back to running

- transitions waiting_target back to running
   - Expected: resumed.status equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions waiting_target back to running")
var job = make_job("job_9", "s1", "t32_cmd_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_target")
val resumed = try_transition(job, "running")
expect(resumed.status).to_equal("running")
```

</details>

#### transitions running to waiting_practice

- transitions running to waiting_practice
   - Expected: waiting.status equals `waiting_practice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("transitions running to waiting_practice")
var job = make_job("job_10", "s1", "t32_cmm_run")
job = try_transition(job, "running")
val waiting = try_transition(job, "waiting_practice")
expect(waiting.status).to_equal("waiting_practice")
```

</details>

#### invalid transitions

#### rejects completed to running

- rejects completed to running
   - Expected: invalid.status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects completed to running")
var job = make_job("job_11", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "completed")
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("completed")
```

</details>

#### rejects failed to running

- rejects failed to running
   - Expected: invalid.status equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects failed to running")
var job = make_job("job_12", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "failed")
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("failed")
```

</details>

#### rejects timed_out to running

- rejects timed_out to running
   - Expected: invalid.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects timed_out to running")
var job = make_job("job_13", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "timed_out")
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("timed_out")
```

</details>

#### rejects cancelled to running

- rejects cancelled to running
   - Expected: invalid.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects cancelled to running")
var job = make_job("job_14", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "cancelled")
val invalid = try_transition(job, "running")
expect(invalid.status).to_equal("cancelled")
```

</details>

#### rejects queued to completed directly

- rejects queued to completed directly
   - Expected: invalid.status equals `queued`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects queued to completed directly")
val job = make_job("job_15", "s1", "t32_cmm_run")
val invalid = try_transition(job, "completed")
expect(invalid.status).to_equal("queued")
```

</details>

#### allows queued to cancelled

- allows queued to cancelled
   - Expected: cancelled.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows queued to cancelled")
val job = make_job("job_16", "s1", "t32_cmm_run")
val cancelled = try_transition(job, "cancelled")
expect(cancelled.status).to_equal("cancelled")
```

</details>

### T32 Job Manager Operations

#### job creation via manager

#### creates job and increments counter

- creates job and increments counter
   - Expected: result1[0] equals `job_1`
   - Expected: result1[1] equals `ok`
   - Expected: result2[0] equals `job_2`
   - Expected: result2[1] equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates job and increments counter")
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

- assigns unique ids across sessions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("assigns unique ids across sessions")
var mgr = make_manager()
val r1 = manager_create_job(mgr, "s1", "t32_cmm_run", false)
val r2 = manager_create_job(mgr, "s2", "t32_cmm_run", false)
expect(r1[0]).to_not_equal(r2[0])
```

</details>

#### listing jobs

#### lists all active jobs

- lists all active jobs
   - Expected: active.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists all active jobs")
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
manager_create_job(mgr, "s1", "t32_cmd_run", false)
manager_create_job(mgr, "s2", "t32_eval", false)
val active = manager_list_jobs(mgr)
expect(active.len()).to_equal(3)
```

</details>

#### filters jobs by session_id

- filters jobs by session_id
   - Expected: s1_jobs.len() equals `2`
   - Expected: s1_jobs[0].session_id equals `s1`
   - Expected: s1_jobs[1].session_id equals `s1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters jobs by session_id")
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

- excludes terminal jobs from active list
   - Expected: active.len() equals `1`
   - Expected: active[0].job_id equals `job_1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("excludes terminal jobs from active list")
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

- returns correct job by id
   - Expected: job.job_id equals `job_2`
   - Expected: job.session_id equals `s2`
   - Expected: job.tool_name equals `t32_cmd_run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns correct job by id")
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

- returns not_found sentinel for nonexistent id
   - Expected: job.job_id equals ``
   - Expected: job.status equals `not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns not_found sentinel for nonexistent id")
var mgr = make_manager()
val job = manager_get_job(mgr, "job_999")
expect(job.job_id).to_equal("")
expect(job.status).to_equal("not_found")
```

</details>

#### cancelling jobs

#### cancels a queued job

- cancels a queued job
   - Expected: ok is true
   - Expected: job.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cancels a queued job")
var mgr = make_manager()
manager_create_job(mgr, "s1", "t32_cmm_run", false)
val ok = manager_cancel_job(mgr, "job_1")
expect(ok).to_equal(true)
val job = manager_get_job(mgr, "job_1")
expect(job.status).to_equal("cancelled")
```

</details>

#### cancels a running job

- cancels a running job
   - Expected: ok is true
   - Expected: job.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cancels a running job")
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

- rejects cancel on completed job
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects cancel on completed job")
var mgr = make_manager_with_completed_job()
val ok = manager_cancel_job(mgr, "job_1")
expect(ok).to_equal(false)
```

</details>

#### concurrent limit

#### enforces max 16 concurrent jobs

- enforces max 16 concurrent jobs
   - Expected: r[1] equals `ok`
   - Expected: overflow[0] equals ``
   - Expected: overflow[1] equals `error:max_concurrent_exceeded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enforces max 16 concurrent jobs")
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

- allows new jobs after terminal transitions free slots
   - Expected: r[1] equals `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows new jobs after terminal transitions free slots")
var mgr = make_manager_with_16_jobs_first_completed()
val r = manager_create_job(mgr, "s1", "t32_cmm_run", false)
expect(r[1]).to_equal("ok")
```

</details>

#### cleanup

#### removes expired terminal jobs

- removes expired terminal jobs
   - Expected: removed equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes expired terminal jobs")
var mgr = make_manager_with_expired_completed_job()
val removed = manager_cleanup(mgr, 400000)
expect(removed).to_equal(1)
```

</details>

#### preserves active jobs during cleanup

- preserves active jobs during cleanup
   - Expected: removed equals `0`
   - Expected: mgr.jobs.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves active jobs during cleanup")
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

- background true returns immediately with job_id
   - Expected: result[0] equals `job_1`
   - Expected: result[1] equals `ok`
   - Expected: job.background is true
   - Expected: job.status equals `queued`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("background true returns immediately with job_id")
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

- foreground job also gets job_id for timeout continuation
   - Expected: result[0] equals `job_1`
   - Expected: job.background is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("foreground job also gets job_id for timeout continuation")
var mgr = make_manager()
val result = manager_create_job(mgr, "s1", "t32_cmm_run", false)
expect(result[0]).to_equal("job_1")
val job = manager_get_job(mgr, "job_1")
expect(job.background).to_equal(false)
```

</details>

#### polling

#### poll returns pending for queued job

- poll returns pending for queued job
   - Expected: poll_status(job) equals `pending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("poll returns pending for queued job")
val job = make_job("job_1", "s1", "t32_cmm_run")
expect(poll_status(job)).to_equal("pending")
```

</details>

#### poll returns pending for running job

- poll returns pending for running job
   - Expected: poll_status(job) equals `pending`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("poll returns pending for running job")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
expect(poll_status(job)).to_equal("pending")
```

</details>

#### poll returns completed for finished job

- poll returns completed for finished job
   - Expected: poll_status(job) equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("poll returns completed for finished job")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "completed")
expect(poll_status(job)).to_equal("completed")
```

</details>

#### poll returns failed for error job

- poll returns failed for error job
   - Expected: poll_status(job) equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("poll returns failed for error job")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "failed")
expect(poll_status(job)).to_equal("failed")
```

</details>

#### result availability

#### result available after completion

- result available after completion
   - Expected: result_available(job) is true
   - Expected: job.result_text equals `Flash programming complete`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result available after completion")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = set_result(job, "Flash programming complete")
job = try_transition(job, "completed")
expect(result_available(job)).to_equal(true)
expect(job.result_text).to_equal("Flash programming complete")
```

</details>

#### result not available while running

- result not available while running
   - Expected: result_available(job) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result not available while running")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
expect(result_available(job)).to_equal(false)
```

</details>

#### result available after failure with error

- result available after failure with error
   - Expected: result_available(job) is true
   - Expected: job.error_message equals `connection lost`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result available after failure with error")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition_with_error(job, "failed", "connection lost")
expect(result_available(job)).to_equal(true)
expect(job.error_message).to_equal("connection lost")
```

</details>

#### resource URI

#### produces correct resource URI format

- produces correct resource URI format
   - Expected: uri equals `t32://jobs/job_42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces correct resource URI format")
val uri = job_resource_uri("job_42")
expect(uri).to_equal("t32://jobs/job_42")
```

</details>

#### URI starts with t32 scheme

- URI starts with t32 scheme


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("URI starts with t32 scheme")
val uri = job_resource_uri("job_1")
expect(uri).to_start_with("t32://")
```

</details>

#### URI contains jobs path

- URI contains jobs path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("URI contains jobs path")
val uri = job_resource_uri("job_123")
expect(uri).to_contain("/jobs/")
```

</details>

### T32 Job Timeout Policy

#### default timeouts per tool type

#### cmm_run has 60s default timeout

- cmm_run has 60s default timeout
   - Expected: default_timeout_for_tool("t32_cmm_run") equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cmm_run has 60s default timeout")
expect(default_timeout_for_tool("t32_cmm_run")).to_equal(60000)
```

</details>

#### cmd_run has 10s default timeout

- cmd_run has 10s default timeout
   - Expected: default_timeout_for_tool("t32_cmd_run") equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cmd_run has 10s default timeout")
expect(default_timeout_for_tool("t32_cmd_run")).to_equal(10000)
```

</details>

#### eval has 3s default timeout

- eval has 3s default timeout
   - Expected: default_timeout_for_tool("t32_eval") equals `3000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eval has 3s default timeout")
expect(default_timeout_for_tool("t32_eval")).to_equal(3000)
```

</details>

#### window_capture has 5s default timeout

- window_capture has 5s default timeout
   - Expected: default_timeout_for_tool("t32_window_capture") equals `5000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("window_capture has 5s default timeout")
expect(default_timeout_for_tool("t32_window_capture")).to_equal(5000)
```

</details>

#### screenshot has 10s default timeout

- screenshot has 10s default timeout
   - Expected: default_timeout_for_tool("t32_screenshot") equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("screenshot has 10s default timeout")
expect(default_timeout_for_tool("t32_screenshot")).to_equal(10000)
```

</details>

#### flash_program has 120s default timeout

- flash_program has 120s default timeout
   - Expected: default_timeout_for_tool("t32_flash_program") equals `120000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flash_program has 120s default timeout")
expect(default_timeout_for_tool("t32_flash_program")).to_equal(120000)
```

</details>

#### unknown tool gets default 10s timeout

- unknown tool gets default 10s timeout
   - Expected: default_timeout_for_tool("t32_unknown") equals `10000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unknown tool gets default 10s timeout")
expect(default_timeout_for_tool("t32_unknown")).to_equal(10000)
```

</details>

#### custom timeout override

#### custom timeout_ms overrides default

- custom timeout_ms overrides default
   - Expected: custom_job.timeout_ms equals `30000`
   - Expected: default_timeout_for_tool("t32_cmm_run") equals `60000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("custom timeout_ms overrides default")
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

- timed out status set correctly on timeout
   - Expected: job.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("timed out status set correctly on timeout")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "timed_out")
expect(job.status).to_equal("timed_out")
```

</details>

#### timeout does not affect background job flag

- timeout does not affect background job flag
   - Expected: job.status equals `timed_out`
   - Expected: job.background is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("timeout does not affect background job flag")
var job = make_bg_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "timed_out")
expect(job.status).to_equal("timed_out")
expect(job.background).to_equal(true)
```

</details>

#### timed_out is a terminal state

- timed_out is a terminal state
   - Expected: invalid.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("timed_out is a terminal state")
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

- waiting_practice can complete directly
   - Expected: job.status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("waiting_practice can complete directly")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_practice")
job = try_transition(job, "completed")
expect(job.status).to_equal("completed")
```

</details>

#### waiting_practice can fail

- waiting_practice can fail
   - Expected: job.status equals `failed`
   - Expected: job.error_message equals `PRACTICE error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("waiting_practice can fail")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_practice")
job = try_transition_with_error(job, "failed", "PRACTICE error")
expect(job.status).to_equal("failed")
expect(job.error_message).to_equal("PRACTICE error")
```

</details>

#### waiting_target can time out

- waiting_target can time out
   - Expected: job.status equals `timed_out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("waiting_target can time out")
var job = make_job("job_1", "s1", "t32_cmd_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_target")
job = try_transition(job, "timed_out")
expect(job.status).to_equal("timed_out")
```

</details>

#### waiting_target can be cancelled

- waiting_target can be cancelled
   - Expected: job.status equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("waiting_target can be cancelled")
var job = make_job("job_1", "s1", "t32_cmd_run")
job = try_transition(job, "running")
job = try_transition(job, "waiting_target")
job = try_transition(job, "cancelled")
expect(job.status).to_equal("cancelled")
```

</details>

#### manager with mixed sessions

#### handles multiple sessions independently

- handles multiple sessions independently
   - Expected: a_jobs.len() equals `2`
   - Expected: b_jobs.len() equals `1`
   - Expected: a_jobs[0].tool_name equals `t32_cmm_run`
   - Expected: a_jobs[1].tool_name equals `t32_eval`
   - Expected: b_jobs[0].tool_name equals `t32_cmd_run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple sessions independently")
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

- result persists through completion
   - Expected: job.result_text equals `DO flash_program.cmm completed successfully`
   - Expected: job.status equals `completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result persists through completion")
var job = make_job("job_1", "s1", "t32_cmm_run")
job = try_transition(job, "running")
job = set_result(job, "DO flash_program.cmm completed successfully")
job = try_transition(job, "completed")
expect(job.result_text).to_equal("DO flash_program.cmm completed successfully")
expect(job.status).to_equal("completed")
```

</details>

#### error message persists on failure

- error message persists on failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("error message persists on failure")
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
| Source | `test/unit/app/mcp_t32/mcp_t32_job_manager_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Job Lifecycle, T32 Job Manager Operations, T32 Background Execution Model, T32 Job Timeout Policy, T32 Job Manager Edge Cases.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-UNIT)`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ebc6b36730ac48e24c7b4a3b65d55d05ef164f6b2a5ba4b9cc10461fc76eae86`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ebc6b36730ac48e24c7b4a3b65d55d05ef164f6b2a5ba4b9cc10461fc76eae86`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ebc6b36730ac48e24c7b4a3b65d55d05ef164f6b2a5ba4b9cc10461fc76eae86`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_t32/mcp_t32_job_manager_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_job_manager_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_job_manager_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_job_manager_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_job_manager_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 17 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_t32/mcp_t32_job_manager_spec.spl:356:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates job with valid id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_job_manager_spec.spl:364:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts in queued status' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_job_manager_spec.spl:371:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'transitions queued to running' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

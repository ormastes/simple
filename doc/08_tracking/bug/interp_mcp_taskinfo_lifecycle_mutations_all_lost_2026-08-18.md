# MCP `TaskManager` lifecycle is a complete no-op in the interpreter — results and error text silently discarded

- **Status:** OPEN
- **Filed:** 2026-08-18
- **Severity:** HIGH (silent data loss across an entire subsystem)
- **Evidence bar:** **SOURCE-VERIFIED, NOT EXECUTION-VERIFIED**
- **Root cause:** `doc/08_tracking/bug/interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`
- **Triage:** `scratchpad/sessions/aliasing_unprotected_sites_triage.md` (cluster 2)

## Sites (verified)

`src/lib/nogc_async_mut/mcp/tasks.spl` — every mutating method of `TaskManager`:

| method | bind | lost write(s) |
|---|---|---|
| `cancel_task`     | 108 | 109 |
| `start_task`      | 117 | 118 |
| `complete_task`   | 123 | 124, 125, 126 |
| `fail_task`       | 131 | 132, 133 |
| `update_progress` | 138 | 139, 140 |

`TaskInfo` is a **class** (`tasks.spl:27`); `self.tasks` is a `Dict`-valued
field. Element read from the dict yields a copy under the interpreter.

## Code shape

```simple
    me complete_task(id: String, result_json: String):
        if self.tasks.contains_key(id):
            val task = self.tasks[id]           # <- COPY in the interpreter
            task.state = TaskState.Completed    # <- lost
            task.result_json = result_json      # <- lost
            task.progress = task.total          # <- lost
```

No `self.tasks[id] = task` write-back exists in any of the five methods.

## User-visible symptom

The task lifecycle never advances. Every task stays in whatever state it was
registered with: `start_task` does nothing, `cancel_task` **returns `true`**
while the task keeps running state, `complete_task` discards the entire result
payload, `fail_task` discards the error text. `get_task` and `list_tasks_json`
therefore report every task as perpetually pending with empty results. Callers
that poll for completion never observe it; callers that surface `error_msg` show
an empty string for a genuinely failed task. Because `cancel_task` still returns
`true`, the failure is actively misreported rather than merely absent.

## Engine matrix

| engine | status |
|---|---|
| tree-walk interpreter | **BROKEN** |
| JIT | correct |
| native | correct |

Interpreter-only: class values are `Value::Object` (the copy-on-write STRUCT
carrier) because `Value::ClassInstance` has ZERO producers; identity is faked by
path-based write-back at ~14 assignment sites, which does not cover
bind-then-mutate.

## Minimal repro (from source reasoning, not executed)

```simple
class Info:
    state: i64

class Mgr:
    tasks: {text: Info}

impl Mgr:
    me finish(id: text):
        if self.tasks.contains_key(id):
            val t = self.tasks[id]
            t.state = 2

fn main():
    val m = Mgr(tasks: {"a": Info(state: 0)})
    m.finish("a")
    print("expect 2, got {m.tasks["a"].state}")
```

## Command that would settle it

```bash
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <repro>.spl
SIMPLE_EXECUTION_MODE=jit         bin/simple run <repro>.spl   # control
```

Not run: `bin/simple` is the Rust seed and the host is saturated.

## Reachability

**Not measured.** Interpreter reachability was INFERRED from test references in
the triage, not observed. Note the dict carrier adds a second unknown: whether
dict-element reads take the same copying path as list-element reads has been
reasoned from the shared `Value::Object` representation, not demonstrated.

## Correct fix

Engine fix — construct `Value::ClassInstance` in the interpreter. Do **not** add
`self.tasks[id] = task` write-backs to these five methods; a local write-back
papers over the engine defect, as the canonical record states explicitly.

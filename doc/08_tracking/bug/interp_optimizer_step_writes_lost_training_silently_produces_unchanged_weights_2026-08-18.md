# Optimizer `step()` writes to `param.value` are lost in the interpreter — training silently produces UNCHANGED WEIGHTS

- **Status:** OPEN
- **Filed:** 2026-08-18
- **Severity:** CRITICAL (silent, plausible wrong answer — the worst failure mode in this family)
- **Evidence bar:** **SOURCE-VERIFIED, NOT EXECUTION-VERIFIED** (see below)
- **Root cause:** `doc/08_tracking/bug/interp_list_class_element_read_returns_copy_mutation_loss_2026-08-17.md`
- **Triage:** `scratchpad/sessions/aliasing_unprotected_sites_triage.md` (cluster 1 of 13 CRITICAL unprotected sites)

## Sites (verified by reading the file)

`src/lib/gc_async_mut/pure/training.spl`

| optimizer | bind | lost write(s) |
|---|---|---|
| `SGD.step`     | 225 | 243 |
| `Adam.step`    | 290 | 322 |
| `RMSprop.step` | 352 | 364 |
| `AdamW.step`   | 397 | 400, 418 |

`Tensor` is a **class** (`src/lib/gc_async_mut/pure/autograd.spl:54`), and
`self.parameters` is a list field, so this is exactly the canonical shape.

## Code shape (bind-then-mutate, no write-back)

```simple
    me step():
        var i = 0
        while i < self.parameters.len():
            val param = self.parameters[i]          # <- COPY in the interpreter
            if param.grad.?:
                ...
                param.value = tensor_sub(param.value, v_new)   # <- lost
            i = i + 1
```

There is no `self.parameters[i] = param` anywhere in the file — confirmed by
grepping every `param.value` occurrence; the only writes are the four above and
read-only `tensor_zeros_like(param.value)` calls in the constructors.

## User-visible symptom

Training runs to completion, loss is computed, and the moment/velocity buffers
(`self.m`, `self.v`, `self.velocity`) **do** update because they are the
optimizer's own fields mutated through `self`, which is the protected path. Only
the parameter tensors are frozen. So the run looks like it is learning — it
prints step counts, it consumes time, momentum state evolves — while the model
is bit-identical to its initialization. No error, no warning, no diagnostic.
An unchanged model that reports a training loop as successful is materially
worse than a crash: it is a convincing lie that survives review.

## Engine matrix

| engine | status |
|---|---|
| tree-walk interpreter (`bin/simple test`, `SIMPLE_EXECUTION_MODE=interpreter`) | **BROKEN** |
| JIT | correct |
| native | correct |

Interpreter-only, because only the interpreter represents `class` values as
`Value::Object` (the copy-on-write STRUCT carrier). `Value::ClassInstance` has
ZERO producers; class identity is faked by path-based write-back at ~14
assignment sites, which covers in-place chained mutation but not
bind-then-mutate.

## Minimal repro (constructed from source reasoning, not executed)

```simple
class T:
    value: i64

class Opt:
    params: [T]

impl Opt:
    me step():
        var i = 0
        while i < self.params.len():
            val p = self.params[i]
            p.value = p.value - 1
            i = i + 1

fn main():
    val o = Opt(params: [T(value: 100)])
    o.step()
    o.step()
    print("expect 98, got {o.params[0].value}")
```

Expected `98`; predicted interpreter output `100`.

## Command that would settle it

```bash
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <repro>.spl
SIMPLE_EXECUTION_MODE=jit         bin/simple run <repro>.spl   # control: must print 98
```

Not run here: `bin/simple` currently resolves to the Rust seed and the box is
saturated by other bootstrap lanes.

## Reachability

**Not measured.** The triage INFERRED interpreter reachability from test
references only. Whether any currently-green test actually executes
`SGD/Adam/RMSprop/AdamW.step` under the interpreter is unestablished — a green
suite is not evidence that this path is exercised, and given the symptom it may
well be green *because* nothing asserts on post-step weights.

## Correct fix

The fix is the **engine fix**: make the interpreter construct
`Value::ClassInstance` for class values so element reads alias instead of
snapshotting. Do **not** add `self.parameters[i] = param` write-backs here. A
local write-back would make these four call sites pass while leaving the engine
defect in place for every other unprotected site, and would remove the strongest
symptom that motivates fixing it — i.e. it masks the defect rather than fixing
it.

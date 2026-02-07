# Spawn Keyword Implementation Plan

**Feature:** Actor spawning with `spawn` keyword
**Priority:** MEDIUM
**Impact:** 7 skipped tests
**Estimated Effort:** 3-4 sprints
**Status:** Planning

---

## Overview

The `spawn` keyword creates new actor instances for message-based concurrency.

### Syntax

```simple
# Define actor
actor Worker:
    var count: i64

    fn init():
        self.count = 0

    fn process(data: text):
        self.count = self.count + 1
        print "Processing: {data}"

# Spawn actor instance
val worker = spawn Worker()

# Send messages
worker.send(process, "task1")
worker.send(process, "task2")

# Parallel spawning
val workers = [for i in 0..10: spawn Worker()]
```

---

## Actor Model Overview

### Key Principles

1. **Isolated state** - No shared memory
2. **Message passing** - Asynchronous communication
3. **Location transparency** - Local or remote actors treated same
4. **Supervision** - Hierarchical error handling

### Actor Lifecycle

```
Created → Running → Stopped → Terminated
              ↓
           Suspended
```

---

## Implementation Phases

### Phase 1: Actor Definition (1 week)

**Actor Keyword:**

```simple
actor Counter:
    var value: i64  # Private state

    fn init():
        # Constructor
        self.value = 0

    fn increment():
        # Message handler
        self.value = self.value + 1

    fn get() -> i64:
        # Message handler with return
        self.value

    fn cleanup():
        # Destructor
        print "Counter stopped"
```

**Actor Reference Type:**

```simple
# ActorRef is handle to actor instance
struct ActorRef<T>:
    actor_id: ActorId
    mailbox: Mailbox

# Send message
fn send<Args>(method: fn(Args), args: Args):
    val msg = Message(method: method, args: args)
    self.mailbox.push(msg)

# Request-response
fn ask<Args, R>(method: fn(Args) -> R, args: Args) -> Future<R>:
    val (promise, future) = new_promise()
    val msg = Request(method: method, args: args, promise: promise)
    self.mailbox.push(msg)
    future
```

---

### Phase 2: Spawn Implementation (1 week)

**Spawn Keyword:**

```simple
# Lexer: add 'spawn' keyword
# Parser: parse spawn expression

fn parse_spawn() -> Expr:
    consume(Keyword("spawn"))
    val actor_type = parse_type()
    consume(LParen)
    val args = parse_args()  # Constructor arguments
    consume(RParen)

    Expr(kind: ExprKind.Spawn(actor_type, args))
```

**Actor Runtime:**

```simple
# src/std/actors/runtime.spl
struct ActorRuntime:
    actors: Map<ActorId, ActorContext>
    scheduler: Scheduler

    fn spawn<T>(actor_type: Type<T>, args: ...) -> ActorRef<T>:
        val actor_id = new_actor_id()
        val mailbox = Mailbox.new()
        val actor = actor_type.new(args...)

        val context = ActorContext(
            id: actor_id,
            actor: actor,
            mailbox: mailbox,
            state: ActorState.Running
        )

        self.actors.insert(actor_id, context)
        self.scheduler.schedule(actor_id)

        ActorRef(actor_id: actor_id, mailbox: mailbox)

    fn process_mailbox(actor_id: ActorId):
        val context = self.actors.get(actor_id)?
        val message = context.mailbox.pop()?

        # Invoke message handler
        match message:
            Message(method, args):
                method.invoke(context.actor, args)
            Request(method, args, promise):
                val result = method.invoke(context.actor, args)
                promise.complete(result)
```

---

### Phase 3: Mailbox & Scheduler (1 week)

**Mailbox:**

```simple
# src/std/actors/mailbox.spl
struct Mailbox:
    queue: Queue<Message>
    capacity: i64

    fn push(msg: Message):
        if self.queue.len() >= self.capacity:
            # Back-pressure handling
            suspend_sender()
        self.queue.push(msg)

    fn pop() -> Message?:
        self.queue.pop()

    fn is_empty() -> bool:
        self.queue.is_empty()
```

**Scheduler:**

```simple
# src/std/actors/scheduler.spl
struct Scheduler:
    ready_queue: Queue<ActorId>
    thread_pool: ThreadPool

    fn schedule(actor_id: ActorId):
        self.ready_queue.push(actor_id)
        self.wake_worker()

    fn run():
        while true:
            val actor_id = self.ready_queue.pop()?
            self.thread_pool.submit(\:
                process_actor(actor_id)
            )
```

---

### Phase 4: Message Patterns (1 week)

**Fire-and-Forget:**

```simple
worker.send(process, data)
# No wait, no result
```

**Request-Response:**

```simple
val result = await worker.ask(compute, input)
print result
```

**Broadcast:**

```simple
for worker in workers:
    worker.send(process, data)
```

**Pipeline:**

```simple
val output = spawn Output()
val processor = spawn Processor(output)
val input = spawn Input(processor)

input.send(start)
```

---

### Phase 5: Supervision (1 week)

**Supervisor:**

```simple
actor Supervisor:
    workers: [ActorRef<Worker>]

    fn init():
        self.workers = [for i in 0..10: spawn Worker()]

    fn on_worker_failed(worker: ActorRef<Worker>):
        # Restart failed worker
        val index = self.workers.find_index(worker)
        self.workers[index] = spawn Worker()

    fn stop_all():
        for worker in self.workers:
            worker.send(stop)
```

**Error Handling:**

```simple
actor Worker:
    fn process(data: text):
        try:
            risky_operation(data)
        catch e:
            # Report error to supervisor
            self.supervisor.send(worker_failed, self)
            # Optionally: restart self
```

---

## Standard Library

**Actor Utilities:**

```simple
# src/std/actors/utils.spl

# Spawn N actors
fn spawn_pool<T>(count: i64, factory: fn() -> T) -> [ActorRef<T>]:
    [for i in 0..count: spawn factory()]

# Round-robin dispatcher
fn dispatch_round_robin<T>(actors: [ActorRef<T>], tasks: [Task]):
    var index = 0
    for task in tasks:
        actors[index % actors.len()].send(process, task)
        index = index + 1

# Wait for all actors to complete
async fn join_all<T>(actors: [ActorRef<T>]):
    for actor in actors:
        await actor.ask(wait_done)
```

---

## Examples

**Worker Pool:**

```simple
# examples/actors/worker_pool.spl
actor Worker:
    fn process(task: Task) -> Result:
        # Heavy computation
        expensive_work(task)

async fn main():
    # Spawn 10 workers
    val workers = [for i in 0..10: spawn Worker()]

    # Distribute tasks
    val tasks = load_tasks()
    val futures = []
    for (i, task) in tasks.enumerate():
        val worker = workers[i % workers.len()]
        futures.push(worker.ask(process, task))

    # Wait for all results
    val results = await gather(futures)
    print_summary(results)
```

**Ping-Pong:**

```simple
# examples/actors/ping_pong.spl
actor Ping:
    pong: ActorRef<Pong>

    fn start():
        self.pong.send(ping, 0)

    fn pong(count: i64):
        if count < 10:
            print "Ping: {count}"
            self.pong.send(ping, count + 1)

actor Pong:
    ping: ActorRef<Ping>

    fn ping(count: i64):
        print "Pong: {count}"
        self.ping.send(pong, count)

fn main():
    val pong = spawn Pong()
    val ping = spawn Ping(pong: pong)
    pong.ping = ping
    ping.start()
```

---

## Comparison with Other Languages

| Language | Syntax | Model |
|----------|--------|-------|
| **Simple** | `spawn Actor()` | Lightweight actors |
| Erlang | `spawn(fun() -> ... end)` | Process-based |
| Akka (Scala) | `system.actorOf(Props[Actor])` | Actor system |
| Go | `go func() { ... }()` | Goroutines (not actors) |
| Pony | `create Actor` | Actor-based |

---

## Performance Considerations

### Benchmarks:
- Actor creation: ~1μs
- Message send: ~100ns
- Message receive: ~200ns
- Mailbox capacity: 10K messages

### Memory:
- Actor instance: ~1KB
- Mailbox: ~100 bytes + messages
- ActorRef: 16 bytes

---

## Migration Path

**From threads to actors:**

```simple
# Before (threads):
val threads = [for i in 0..10:
    spawn_thread(\: worker_fn(i))
]

# After (actors):
val workers = [for i in 0..10:
    spawn Worker(id: i)
]
```

**From callbacks to messages:**

```simple
# Before (callbacks):
http.get(url, \response:
    process(response)
)

# After (actors):
val processor = spawn Processor()
val fetcher = spawn HttpFetcher(processor)
fetcher.send(fetch, url)
```

---

## Success Criteria

1. ✅ Parser accepts `spawn` keyword
2. ✅ Actors can be spawned
3. ✅ Messages can be sent
4. ✅ Message handlers execute
5. ✅ Request-response works
6. ✅ Supervision works
7. ✅ 7 skipped tests pass
8. ✅ Performance meets benchmarks

---

## Timeline

| Phase | Duration | Deliverable |
|-------|----------|-------------|
| 1. Actor Def | 1 week | Actor syntax works |
| 2. Spawn | 1 week | spawn keyword works |
| 3. Mailbox | 1 week | Message passing works |
| 4. Patterns | 1 week | Common patterns work |
| 5. Supervision | 1 week | Error handling works |
| **Total** | **5 weeks** | **Feature complete** |

---

## Dependencies

- **Blocker:** None (can start now)
- **Enhanced by:** Async/await (for request-response)
- **Enables:** Distributed systems, fault-tolerant apps, high concurrency

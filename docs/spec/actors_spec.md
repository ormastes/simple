# actors_spec

*Source: `simple/std_lib/test/features/concurrency/actors_spec.spl`*

---

Actors - Feature #40

Overview:
    Actor-based concurrency with spawn keyword. Actors run in isolation with
    message passing for communication. This is the default concurrency mode
    for Simple programs, providing data race safety by design.

Syntax:
    fn worker():                    # Define worker function
        return compute_something()

    val handle = spawn worker()     # Spawn actor

Implementation:
    - Actor mode is the default concurrency mode
    - spawn creates new actor from function
    - Actors run in isolation (no shared memory)
    - Rejects mut T in parameters for safety
    - Data is copied between actors
    - Message passing via send/receive (pending)

Notes:
    - Actor mode is the default
    - Rejects mut T in parameters for data race safety
    - Send/receive pending implementation
    - Complete: spawn
    - Pending: send/receive, actor state, supervision

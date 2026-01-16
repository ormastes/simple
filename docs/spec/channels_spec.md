# Type-safe Channels

*Source: `simple/std_lib/test/features/language/channels_spec.spl`*

---

# Type-safe Channels

**Feature ID:** Channels
**Category:** Language - Concurrency
**Difficulty:** 3/5
**Status:** Planned

## Overview

Channels provide typed, thread-safe communication between isolated threads.
Simple extends the basic channel concept with **direction types** that prevent
misuse at compile time.

## Channel Types

**Basic Channel:**
```simple
val ch = Channel.new()
ch.send(42)
val v = ch.recv()
```

**Direction Types (Proposed):**
```simple
val (tx, rx) = typed_channel<i32>()
tx.send(42)       # Sender - can only send
val v = rx.recv() # Receiver - can only receive
```

**Operator Syntax (Proposed):**
```simple
tx.send(42)       # Method style (always works)
val v = <-rx      # Prefix operator for receive (LL(1) safe)
```

## Key Features

- **Type Safety:** Channels are parameterized by element type
- **Direction Types:** Sender<T> and Receiver<T> prevent misuse
- **Thread Safety:** All channel operations are synchronized
- **Blocking/Non-blocking:** recv() blocks, try_recv() returns Option

## Channel Variants

1. **UnboundedChannel<T>** - No capacity limit
2. **BoundedChannel<T>** - Fixed capacity, backpressure
3. **Oneshot<T>** - Single value transfer

## Implementation

**Primary Files:**
- `simple/std_lib/src/concurrency/channels.spl` - Channel types
- `src/runtime/src/value/channels.rs` - Channel FFI

**Dependencies:**
- Feature: Generics (parameterized types)
- Feature: Threads (inter-thread communication)

## Channel Send and Receive

    Channels provide a synchronized queue for passing values between threads.

    **Basic Operations:**
    ```simple
    val ch = Channel.new()
    ch.send(42)           # Put value in channel
    val v = ch.recv()     # Take value from channel
    ```

    **Semantics:**
    - `send()` - Non-blocking for unbounded, may block for bounded
    - `recv()` - Blocks until value available
    - `try_recv()` - Non-blocking, returns Option<T>
    - `close()` - Closes channel, recv returns None after drain

**Given** a channel
        **When** sending a value then receiving
        **Then** receives the sent value

        **Example:**
        ```simple
        val ch = Channel.new()
        ch.send(42)
        val v = ch.recv()
        # v = Some(42)
        ```

        **FIFO Ordering:**
        - Values received in order sent
        - First-in, first-out queue semantics

        **Verification:** Received value equals sent value

**Given** a channel with multiple sent values
        **When** receiving multiple times
        **Then** receives values in FIFO order

        **Example:**
        ```simple
        val ch = Channel.new()
        ch.send(1)
        ch.send(2)
        ch.send(3)
        val a = ch.recv()  # 1
        val b = ch.recv()  # 2
        val c = ch.recv()  # 3
        ```

        **Verification:** Values received in order sent

## Sender<T> and Receiver<T>

    Direction types prevent channel misuse at compile time:

    ```simple
    struct Sender<T>:
        _ch: Channel<T>
        fn send(value: T): ...
        # No recv method!

    struct Receiver<T>:
        _ch: Channel<T>
        fn recv() -> Option<T>: ...
        # No send method!
    ```

    **Benefits:**
    - **Compile-time safety:** Can't call recv on sender
    - **API clarity:** Function signatures show intent
    - **Deadlock prevention:** Harder to misuse channels

    **Factory Function:**
    ```simple
    fn typed_channel<T>() -> (Sender<T>, Receiver<T>):
        val ch = Channel.new()
        return (Sender(_ch: ch), Receiver(_ch: ch))
    ```

**Given** a Sender<T> from typed_channel
        **When** attempting to send
        **Then** send succeeds

        **When** attempting to receive
        **Then** compile error (no recv method)

        **Example:**
        ```simple
        val (tx, rx) = typed_channel<i32>()
        tx.send(42)      # OK
        # tx.recv()      # Compile error!
        ```

        **Type Safety:**
        - Sender<T> only has send() method
        - Attempting recv() is compile-time error

        **Verification:** Sender type restricts to send-only

**Given** a Receiver<T> from typed_channel
        **When** attempting to receive
        **Then** receive succeeds

        **When** attempting to send
        **Then** compile error (no send method)

        **Example:**
        ```simple
        val (tx, rx) = typed_channel<i32>()
        tx.send(42)
        val v = rx.recv()  # OK
        # rx.send(10)      # Compile error!
        ```

        **Type Safety:**
        - Receiver<T> only has recv() method
        - Attempting send() is compile-time error

        **Verification:** Receiver type restricts to recv-only

**Given** a call to typed_channel<T>
        **When** destructuring the result
        **Then** get (Sender<T>, Receiver<T>) pair

        **Example:**
        ```simple
        val (tx, rx) = typed_channel<i32>()
        # tx: Sender<i32>
        # rx: Receiver<i32>
        ```

        **Pattern:** Producer/Consumer
        ```simple
        fn producer(out: Sender<i32>):
            for i in 0..10:
                out.send(i)

        fn consumer(inp: Receiver<i32>):
            while true:
                match inp.recv():
                    Some(v): print(v)
                    None: break
        ```

        **Verification:** Factory returns typed pair

## <- Prefix Operator

    The `<-` prefix operator provides Go-style receive syntax:

    ```simple
    val v = <-rx      # Equivalent to rx.recv()
    ```

    **LL(1) Analysis:**
    - Prefix position: `<-` always means receive
    - Single token: Lexer produces CHAN_ARROW
    - Unambiguous: No conflict with comparison

    **Infix Send (Deferred):**
    ```simple
    ch <- 42          # Deferred - lexer ambiguity with a<-b
    ch.send(42)       # Use method instead
    ```

    **Decision:** Only prefix `<-` for receive. Keep `.send()` method.

**Given** a Receiver with a value
        **When** using <-rx syntax
        **Then** receives the value

        **Proposed Syntax:**
        ```simple
        val (tx, rx) = typed_channel<i32>()
        tx.send(42)
        val v = <-rx   # Equivalent to rx.recv()
        ```

        **LL(1) Parsing:**
        1. See `<-` token at expression start
        2. Must be prefix receive operator
        3. Parse following expression as channel

        **Verification:** Prefix <- is unambiguous

**Given** channels in complex expressions
        **When** using <- in expression context
        **Then** composes correctly

        **Examples:**
        ```simple
        val sum = (<-rx1) + (<-rx2)
        val doubled = (<-rx) * 2
        if (<-rx) > threshold: ...
        ```

        **Precedence:**
        - `<-` has high precedence (like prefix !)
        - Parentheses optional in simple cases
        - Required for clarity in complex expressions

        **Verification:** <- works in expressions

## BoundedChannel<T>

    Bounded channels have fixed capacity and provide backpressure:

    ```simple
    val ch = BoundedChannel.new(capacity: 10)
    ch.send(value)    # Blocks if full
    ch.try_send(v)    # Returns false if full
    ```

    **Properties:**
    - `capacity` - Maximum buffered items
    - `is_full()` - Check if at capacity
    - `utilization()` - Buffer usage percentage

    **Use Cases:**
    - Prevent memory exhaustion
    - Rate limiting
    - Producer-consumer with backpressure

**Given** a BoundedChannel with capacity N
        **When** sending N+1 values
        **Then** blocks or returns false on overflow

        **Example:**
        ```simple
        val ch = BoundedChannel.new(capacity: 2)
        ch.send(1)        # OK, buffer: [1]
        ch.send(2)        # OK, buffer: [1, 2]
        ch.try_send(3)    # false, buffer full
        ```

        **Verification:** Bounded channels respect capacity

**Given** a BoundedChannel with items
        **When** checking utilization
        **Then** returns buffer fill percentage

        **Example:**
        ```simple
        val ch = BoundedChannel.new(capacity: 10)
        ch.send(1)
        ch.send(2)
        ch.send(3)
        ch.utilization()  # 0.3 (30% full)
        ```

        **Verification:** Utilization calculated correctly

## Oneshot<T>

    Single-value channels for request-response patterns:

    ```simple
    val (tx, rx) = oneshot<Result>()

    # In worker thread
    go |tx| \\: tx.send(compute_result())

    # In main thread
    val result = rx.recv()
    ```

    **Properties:**
    - Can send exactly one value
    - Second send returns false
    - Perfect for futures/promises pattern

**Given** a Oneshot channel
        **When** sending multiple values
        **Then** only first send succeeds

        **Example:**
        ```simple
        val ch = Oneshot.new()
        ch.send(1)        # true
        ch.send(2)        # false (already completed)
        val v = ch.recv() # Some(1)
        ```

        **Verification:** Second send fails

## WaitGroup = Latch

    Simple's Latch provides WaitGroup functionality:

    ```simple
    val latch = Latch.new(n)

    for i in range(n):
        go(i, latch) \\idx, l:
            work(idx)
            l.countdown()

    latch.wait()  # Blocks until all done
    ```

    **Equivalence:**
    - Go's `WaitGroup.Add(n)` → `Latch.new(n)`
    - Go's `WaitGroup.Done()` → `latch.countdown()`
    - Go's `WaitGroup.Wait()` → `latch.wait()`

**Given** a Latch with count N
        **When** N threads call countdown()
        **Then** wait() unblocks

        **Example:**
        ```simple
        val latch = Latch.new(3)

        for i in 0..3:
            go(i, latch) \\idx, l:
                sleep(idx * 100)
                l.countdown()

        latch.wait()
        print("All done!")
        ```

        **Verification:** Latch synchronizes threads

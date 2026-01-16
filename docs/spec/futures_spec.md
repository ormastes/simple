# futures_spec

*Source: `simple/std_lib/test/features/concurrency/futures_spec.spl`*

---

Futures - Feature #43

Overview:
    Future values representing async computations. Create with future(), resolve
    with await. Supports eager evaluation, value capture, and multiple independent
    futures that can be awaited in any order.

Syntax:
    val f = future(42)                      # Create future from value
    val f = future(expensive_computation()) # Create future from computation
    val result = await f                    # Await future to get value
    val x = await 42                        # Await returns immediately for non-futures

Implementation:
    - Futures evaluate eagerly when created
    - await on future values resolves the computation
    - await on non-future values returns immediately
    - Supports value capture from outer scope
    - Multiple futures can be created and awaited independently
    - Futures can be awaited in any order

Notes:
    - Futures evaluate eagerly when created
    - Await on non-future values returns immediately
    - Supports captured variables
    - Multiple futures can run concurrently

# Host WM SOSIX timer transition

The host compositor performs at most one render turn per call. It returns a
typed SOSIX timer request for the next 16 ms deadline; the scheduler owns
completion and repetition. The compositor contains no sleep or perpetual loop.

Stopped WM state, invalid timer capabilities, and nanosecond deadline overflow
fail closed without scheduling another turn.

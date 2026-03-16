"""Token bucket rate limiter."""

from __future__ import annotations

import time


class RateLimiter:
    """Token bucket rate limiter."""

    def __init__(self, rate: float, capacity: int | None = None) -> None:
        """Initialize rate limiter.

        Args:
            rate: Tokens per second.
            capacity: Max burst capacity. Defaults to rate.
        """
        self._rate = rate
        self._capacity = float(capacity if capacity is not None else int(rate))
        self._tokens = self._capacity
        self._last_refill = time.monotonic()

    def _refill(self) -> None:
        now = time.monotonic()
        elapsed = now - self._last_refill
        self._tokens = min(self._capacity, self._tokens + elapsed * self._rate)
        self._last_refill = now

    def acquire(self) -> None:
        """Acquire a token, blocking if necessary."""
        self._refill()
        while self._tokens < 1:
            deficit = 1 - self._tokens
            time.sleep(deficit / self._rate)
            self._refill()
        self._tokens -= 1


# Pre-configured limiters
scraper_limiter = RateLimiter(rate=30 / 60, capacity=5)   # 30 req/min
api_limiter = RateLimiter(rate=100 / 60, capacity=10)      # 100 req/min

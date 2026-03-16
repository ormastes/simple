"""TTL-based in-memory cache."""

from __future__ import annotations

import time
from typing import Any


class TTLCache:
    """Simple in-memory cache with per-key TTL."""

    # Default TTLs in seconds
    PRICE_TTL = 60        # 1 minute during market hours
    PRICE_TTL_CLOSED = 3600  # 1 hour after market close
    LIST_TTL = 86400      # 24 hours
    NEWS_TTL = 300        # 5 minutes

    def __init__(self, default_ttl: int = 300) -> None:
        self._store: dict[str, tuple[Any, float]] = {}
        self._default_ttl = default_ttl

    def get(self, key: str) -> Any | None:
        """Get a cached value if it exists and hasn't expired."""
        if key not in self._store:
            return None
        value, expires_at = self._store[key]
        if time.time() > expires_at:
            del self._store[key]
            return None
        return value

    def set(self, key: str, value: Any, ttl: int | None = None) -> None:
        """Cache a value with optional TTL override."""
        t = ttl if ttl is not None else self._default_ttl
        self._store[key] = (value, time.time() + t)

    def invalidate(self, key: str) -> None:
        """Remove a specific key from cache."""
        self._store.pop(key, None)

    def clear(self) -> None:
        """Clear all cached values."""
        self._store.clear()

    def _is_market_hours(self) -> bool:
        """Check if Korean market is currently open (KST 09:00-15:30)."""
        import datetime
        import zoneinfo
        kst = zoneinfo.ZoneInfo("Asia/Seoul")
        now = datetime.datetime.now(kst)
        if now.weekday() >= 5:  # Saturday/Sunday
            return False
        market_open = now.replace(hour=9, minute=0, second=0, microsecond=0)
        market_close = now.replace(hour=15, minute=30, second=0, microsecond=0)
        return market_open <= now <= market_close

    def get_price_ttl(self) -> int:
        """Get appropriate price TTL based on market hours."""
        return self.PRICE_TTL if self._is_market_hours() else self.PRICE_TTL_CLOSED


# Global cache instance
cache = TTLCache()

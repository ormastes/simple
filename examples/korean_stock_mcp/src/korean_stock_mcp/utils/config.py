"""Environment variable management and configuration."""

from __future__ import annotations

import os
from pathlib import Path


def _load_dotenv() -> None:
    """Load .env file if it exists (without requiring python-dotenv)."""
    env_path = Path(__file__).resolve().parents[4] / ".env"
    if not env_path.exists():
        return
    with open(env_path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            key, _, value = line.partition("=")
            key, value = key.strip(), value.strip()
            if value and value[0] in ('"', "'") and value[-1] == value[0]:
                value = value[1:-1]
            if key and key not in os.environ:
                os.environ[key] = value


_load_dotenv()


def get_dart_api_key() -> str | None:
    """Get DART API key from environment."""
    return os.environ.get("DART_API_KEY") or None


def get_krx_api_key() -> str | None:
    """Get KRX API key from environment."""
    return os.environ.get("KRX_API_KEY") or None


def get_cache_ttl() -> int | None:
    """Get custom cache TTL override in seconds."""
    val = os.environ.get("KR_STOCK_CACHE_TTL")
    if val:
        try:
            return int(val)
        except ValueError:
            return None
    return None

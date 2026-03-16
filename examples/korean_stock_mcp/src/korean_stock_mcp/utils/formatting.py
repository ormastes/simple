"""Formatting utilities for Korean stock data."""

from __future__ import annotations

from datetime import datetime


def format_krw(amount: float | int) -> str:
    """Format amount as Korean Won."""
    if abs(amount) >= 1_0000_0000:  # 억
        return f"{amount / 1_0000_0000:,.1f}억원"
    if abs(amount) >= 1_0000:  # 만
        return f"{amount / 1_0000:,.0f}만원"
    return f"{amount:,.0f}원"


def format_volume(volume: int) -> str:
    """Format trading volume."""
    if volume >= 1_000_000:
        return f"{volume / 1_000_000:,.1f}M"
    if volume >= 1_000:
        return f"{volume / 1_000:,.1f}K"
    return str(volume)


def format_pct(value: float) -> str:
    """Format percentage change with sign."""
    sign = "+" if value > 0 else ""
    return f"{sign}{value:.2f}%"


def to_yyyymmdd(date: str | datetime) -> str:
    """Convert date to YYYYMMDD format used by pykrx."""
    if isinstance(date, datetime):
        return date.strftime("%Y%m%d")
    # Try common formats
    for fmt in ("%Y-%m-%d", "%Y/%m/%d", "%Y%m%d"):
        try:
            return datetime.strptime(date, fmt).strftime("%Y%m%d")
        except ValueError:
            continue
    return date


def today_yyyymmdd() -> str:
    """Get today's date in YYYYMMDD format."""
    return datetime.now().strftime("%Y%m%d")


def days_ago_yyyymmdd(days: int) -> str:
    """Get date N days ago in YYYYMMDD format."""
    from datetime import timedelta
    return (datetime.now() - timedelta(days=days)).strftime("%Y%m%d")

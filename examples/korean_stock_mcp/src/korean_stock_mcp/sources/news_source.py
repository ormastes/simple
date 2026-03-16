"""News source — RSS feeds and Naver Finance scraping.

Tier 3: No API key required.
"""

from __future__ import annotations

import re
from urllib.parse import quote

import feedparser
import httpx
from bs4 import BeautifulSoup

from korean_stock_mcp.utils.cache import cache, TTLCache
from korean_stock_mcp.utils.rate_limiter import scraper_limiter


def get_market_news(limit: int = 10) -> list[dict]:
    """Get Korean stock market news headlines via Google News RSS.

    Args:
        limit: Maximum number of articles to return.
    """
    cache_key = "market_news"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached[:limit]

    scraper_limiter.acquire()
    query = quote("한국 주식시장")
    url = f"https://news.google.com/rss/search?q={query}&hl=ko&gl=KR&ceid=KR:ko"

    feed = feedparser.parse(url)
    result = []
    for entry in feed.entries[:20]:
        result.append({
            "title": entry.get("title", ""),
            "link": entry.get("link", ""),
            "published": entry.get("published", ""),
            "source": entry.get("source", {}).get("title", ""),
        })

    cache.set(cache_key, result, TTLCache.NEWS_TTL)
    return result[:limit]


def get_stock_news(ticker: str, limit: int = 10) -> list[dict]:
    """Get stock-specific news from Naver Finance.

    Args:
        ticker: 6-digit stock ticker (e.g., "005930")
        limit: Maximum number of articles.
    """
    cache_key = f"stock_news:{ticker}"
    cached = cache.get(cache_key)
    if cached is not None:
        return cached[:limit]

    scraper_limiter.acquire()
    url = f"https://finance.naver.com/item/news_news.naver?code={ticker}&page=1"
    headers = {
        "User-Agent": "Mozilla/5.0 (compatible; KoreanStockMCP/0.1)",
    }

    try:
        with httpx.Client(timeout=15, follow_redirects=True) as client:
            resp = client.get(url, headers=headers)
            resp.raise_for_status()
    except httpx.HTTPError:
        return []

    soup = BeautifulSoup(resp.text, "html.parser")
    result = []

    # Naver Finance news table
    rows = soup.select("table.type5 tr")
    for row in rows:
        title_tag = row.select_one("td.title a")
        date_tag = row.select_one("td.date")
        source_tag = row.select_one("td.info")

        if not title_tag:
            continue

        title = title_tag.get_text(strip=True)
        link = title_tag.get("href", "")
        if link and not link.startswith("http"):
            link = f"https://finance.naver.com{link}"

        result.append({
            "title": title,
            "link": link,
            "date": date_tag.get_text(strip=True) if date_tag else "",
            "source": source_tag.get_text(strip=True) if source_tag else "",
        })

        if len(result) >= 20:
            break

    cache.set(cache_key, result, TTLCache.NEWS_TTL)
    return result[:limit]

# Browser bookmark persistence owner is missing

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Implementation fixed; executable cross-process evidence remains blocked by the
recorded production target compiler/link failure.

## Evidence

`BrowserSession.favorite_links` supports add, update, remove, list, and open,
but it is initialized empty for every new session. No browser/profile owner
serializes it, and no settings facade is connected above BrowserSession.

BrowserSession exposes a typed `BrowserBookmarkSnapshot` load/snapshot
boundary. `BrowserProfileStore` persists at most 256 ordered entries in a
versioned SQLite profile outside BrowserSession, and the hosted registry loads
it only for browser app IDs. Browser-window close saves before destruction;
save failure keeps the window open.

## Ownership constraint

BrowserSession and hostile renderer code must not read or write profile files.
Persistence belongs to a browser-profile broker outside the renderer sandbox.
The hosted web-content registry is currently the only production session owner;
the similarly named UI browser app is a `.ui.sdn` renderer, not browser chrome.

## Implemented fix

`src/os/hosted/browser_profile_store.spl` uses the existing parameterized SQL
facade and transactions. Invalid schemes, oversized rows, duplicate URLs, and
oversized stores fail closed. BrowserSession revalidates every restored URL.

## Required evidence

`browser_profile_store_spec.spl` writes a file-backed profile, closes/reopens
it, restores the bookmark through the hosted registry, removes it, closes the
browser window, and proves a second reopen remains empty. A real target-process
restart is still required before claiming runtime PASS.

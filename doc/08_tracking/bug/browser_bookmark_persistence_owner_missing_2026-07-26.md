# Browser bookmark persistence owner is missing

## Status

Partially resolved; process persistence remains a production blocker for
REQ-WEB-BROWSER-009.

## Evidence

`BrowserSession.favorite_links` supports add, update, remove, list, and open,
but it is initialized empty for every new session. No browser/profile owner
serializes it, and no settings facade is connected above BrowserSession.

BrowserSession now exposes a typed `BrowserBookmarkSnapshot` load/snapshot
boundary. Loading revalidates every URL through the network-navigation policy,
rejects oversized URL/title values, caps the restored set at 256 entries, and
copies arrays across the boundary. The session still performs no profile I/O.

## Ownership constraint

BrowserSession and hostile renderer code must not read or write profile files.
Persistence belongs to a browser-profile broker outside the renderer sandbox.
The hosted web-content registry is currently the only production session owner;
the similarly named UI browser app is a `.ui.sdn` renderer, not browser chrome.

## Required fix

Add a typed bookmark snapshot/load interface between the browser chrome owner
and a bounded profile-settings service. Validate URL schemes through the
existing network navigation boundary, bound entry count and text sizes, write
atomically, and keep malformed records out of BrowserSession.

## Required evidence

A production-surface test must add a bookmark, close the browser process,
restart it with the same profile, list/open the bookmark, remove it, restart
again, and prove it remains removed. In-memory session evidence is not
persistence evidence.

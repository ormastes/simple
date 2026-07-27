# Browser HSTS persistence owner is missing

## Status

Open production blocker for REQ-WEB-BROWSER-011.

## Evidence

BrowserSession enforces bounded in-session `max-age` and `includeSubDomains`
policies, but no browser-profile persistence owner currently stores authenticated
HSTS state across process restarts. No maintained preload-list owner exists.
The only production `BrowserSession` owner is the hosted web-content registry,
which currently creates in-memory sessions without a profile lifecycle.

## Required fix

Persist HSTS policies through the browser profile broker using atomic,
versioned storage. Retain receipt time/expiry, host, and include-subdomain
state; reject corrupt or oversized records. Add a maintained preload update
path if preload support is claimed.

Do not serialize the session-monotonic expiry directly. The profile broker must
own wall-clock receipt/expiry and convert only validated remaining lifetime at
the BrowserSession boundary.

## Required evidence

Prove HTTPS-only policy acquisition, restart persistence, expiry/removal,
subdomain matching, corrupt-store recovery, bounded retention, and no upgrade
from an HTTP-delivered header.

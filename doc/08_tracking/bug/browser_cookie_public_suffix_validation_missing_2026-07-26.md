# Browser cookie public-suffix validation is missing

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Implementation fixed; executable target evidence is compiler-blocked.

## Evidence

`parse_cookie_line_for_url()` checks that a Domain attribute is a suffix of the
response host, but no maintained Public Suffix List owner exists in the
browser stack. A host such as `example.com` can therefore attempt to set
`Domain=com`; multi-label suffixes such as `co.uk` have the same class of risk.

Adjacent parser boundaries are enforced independently: cookie prefixes and
`SameSite=None` are validated, while unsupported partitioned cookies fail
closed rather than silently losing their partition key.

## Required fix

Add one maintained, versioned Public Suffix List owner shared by cookie and
site/origin policy. Reject Domain attributes whose normalized domain is a
public suffix, while preserving valid parent-domain cookies.

## Resolution (2026-07-26)

`common.web.public_suffix` now owns a binary-search lookup generated from the
official Public Suffix List at commit
`e1b8015c3b2f0f4f8c18659c2480fc1a22c07b20` (2026-07-25). The generated
artifact includes ICANN and private rules, wildcard/exception semantics, and
deterministic RFC 3492 ASCII aliases for Unicode rules. Source hash, license,
and a reproducible update command are checked in under
`third_party/public_suffix_list/`.

The shared cookie parser rejects Domain attributes that name a public suffix
or are attached to IPv4/IPv6 hosts, while retaining valid registrable
parent-domain cookies. Host-only cookies remain valid for IP literals.

## Required evidence

Cover single-label and multi-label public suffix rejection, valid registrable
parent-domain acceptance, private suffix policy, IDNA hosts, IP literals, and
PSL version/update provenance.

Focused specs cover each row, but have not been executed because the tracked
target compiler failure exhausted its three allowed repair cycles.

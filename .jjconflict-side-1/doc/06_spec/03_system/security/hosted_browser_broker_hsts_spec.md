# Hosted browser broker HSTS

> Broker-owned HSTS admission and request ordering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Hosted browser broker HSTS

The renderer worker does not own HSTS policy. This scenario enters through the
parent broker boundary used only after an authenticated HTTPS transport
completion. It does not claim that a mock response proves TLS.

## Scenario

### should keep validated HSTS and upgraded requests in the parent broker

1. **Commit a validated HTTPS transport policy**
   - Admit one secure `max-age=60; includeSubDomains` policy.
   - Synchronize its canonical snapshot into the parent registry.
   - Confirm a matching subdomain resolves to HTTPS.
2. **Upgrade a matching HTTP navigation**
   - Open an HTTP child-host URL.
   - Confirm the one-shot navigation permit contains HTTPS.
   - Decode the worker command and confirm it receives only the HTTPS URL.
3. **Upgrade a matching subresource before credentials**
   - Encode the hostile HTTP image request through the real worker protocol and
     enter the broker's production `_dispatch_renderer_fetch` path.
   - Confirm denying CSP produces the exact broker error before the hostile
     script cookie write or any network job.
   - Confirm allowing CSP returns the marked broker-generated HTTPS upgrade
     while no HTTP transport starts and no cookie crosses the HTTP response.
4. **Reject forged or expired policy state**
   - Reject duplicate `max-age`, numeric overflow, plaintext admission,
     expired entries, public suffixes, future receipts, incoherent receipt and
     expiry pairs, and invalid persisted timestamps.
   - Close the process and registry and confirm session HSTS state is released.

**Requirements:** REQ-WEB-BROWSER-010, REQ-WEB-BROWSER-011,
REQ-WEB-BROWSER-012, REQ-WEB-BROWSER-013, REQ-WEB-BROWSER-014,
REQ-WEB-BROWSER-021.

**Runtime status:** Not executed in this lane. The source and manual are ready
for the admitted current pure-Simple runtime gate; no seed/bootstrap substitute
is claimed.

<details>
<summary>Executable SSpec</summary>

Complete runnable source:
`test/03_system/security/hosted_browser_broker_hsts_spec.spl`.

The executable source defines and invokes all frozen helpers:
`setup_broker_hsts_fixture`, `check_hsts_policy_committed`,
`check_navigation_upgraded_before_permit`,
`check_subresource_upgraded_before_credentials`, and
`check_expired_policy_rejected`. It also defines and invokes
`_decode_worker_image_request` for the encoded worker-protocol request.

</details>

</details>

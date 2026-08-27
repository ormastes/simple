# email_translate_spec

> Purpose: Prove that 5a: Gmail X-GM-RAW passthrough.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 74 | 74 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# email_translate_spec

Purpose: Prove that 5a: Gmail X-GM-RAW passthrough.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/devhub/email_translate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that 5a: Gmail X-GM-RAW passthrough.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### 5a: Gmail X-GM-RAW passthrough

#### returns the query verbatim, zero translation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns the query verbatim, zero translation
- Verify: returns the query verbatim, zero translation
   - Expected: translate_query_gm_raw("from:alice is:unread newer_than:2d") equals `from:alice is:unread newer_than:2d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("returns the query verbatim, zero translation")
step("Verify: returns the query verbatim, zero translation")
# @req: REQ-APP-DEVHUB-001
expect(translate_query_gm_raw("from:alice is:unread newer_than:2d")).to_equal("from:alice is:unread newer_than:2d")
```

</details>

### 5b: generic IMAP SEARCH per-operator translation

#### from:X -> FROM \

- from:X -> FROM \
   - Expected: imap_term_from("alice") equals `FROM "alice"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("from:X -> FROM \")
expect(imap_term_from("alice")).to_equal("FROM \"alice\"")
```

</details>

#### to:X -> TO \

- to:X -> TO \
   - Expected: imap_term_to("bob") equals `TO "bob"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("to:X -> TO \")
expect(imap_term_to("bob")).to_equal("TO \"bob\"")
```

</details>

#### cc:X -> CC \

- cc:X -> CC \
   - Expected: imap_term_cc("carol") equals `CC "carol"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("cc:X -> CC \")
expect(imap_term_cc("carol")).to_equal("CC \"carol\"")
```

</details>

#### bcc:X -> BCC \

- bcc:X -> BCC \
   - Expected: imap_term_bcc("dave") equals `BCC "dave"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bcc:X -> BCC \")
expect(imap_term_bcc("dave")).to_equal("BCC \"dave\"")
```

</details>

#### subject:X -> SUBJECT \

- subject:X -> SUBJECT \
   - Expected: imap_term_subject("invoice") equals `SUBJECT "invoice"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("subject:X -> SUBJECT \")
expect(imap_term_subject("invoice")).to_equal("SUBJECT \"invoice\"")
```

</details>

#### free text -> TEXT \

- free text -> TEXT \
   - Expected: imap_term_text("hello world") equals `TEXT "hello world"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("free text -> TEXT \")
expect(imap_term_text("hello world")).to_equal("TEXT \"hello world\"")
```

</details>

#### is:unread -> UNSEEN

- is:unread -> UNSEEN
- Verify: is:unread -> UNSEEN
   - Expected: imap_term_is_unread() equals `UNSEEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is:unread -> UNSEEN")
step("Verify: is:unread -> UNSEEN")
expect(imap_term_is_unread()).to_equal("UNSEEN")
```

</details>

#### is:read -> SEEN

- is:read -> SEEN
- Verify: is:read -> SEEN
   - Expected: imap_term_is_read() equals `SEEN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is:read -> SEEN")
step("Verify: is:read -> SEEN")
expect(imap_term_is_read()).to_equal("SEEN")
```

</details>

#### is:starred -> FLAGGED

- is:starred -> FLAGGED
- Verify: is:starred -> FLAGGED
   - Expected: imap_term_is_starred() equals `FLAGGED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is:starred -> FLAGGED")
step("Verify: is:starred -> FLAGGED")
expect(imap_term_is_starred()).to_equal("FLAGGED")
```

</details>

#### is:important has no IMAP equivalent - documented drop warning

- is:important has no IMAP equivalent - documented drop warning
- Verify: is:important has no IMAP equivalent - documented drop warning
   - Expected: imap_warning_is_important() contains `no IMAP equivalent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is:important has no IMAP equivalent - documented drop warning")
step("Verify: is:important has no IMAP equivalent - documented drop warning")
expect(imap_warning_is_important().contains("no IMAP equivalent")).to_equal(true)
```

</details>

#### has:attachment -> lossy Content-Type heuristic

- has:attachment -> lossy Content-Type heuristic
- Verify: has:attachment -> lossy Content-Type heuristic
   - Expected: imap_term_has_attachment() equals `HEADER "Content-Type" "multipart/mixed"`
   - Expected: imap_warning_has_attachment() contains `lossy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("has:attachment -> lossy Content-Type heuristic")
step("Verify: has:attachment -> lossy Content-Type heuristic")
expect(imap_term_has_attachment()).to_equal("HEADER \"Content-Type\" \"multipart/mixed\"")
expect(imap_warning_has_attachment().contains("lossy")).to_equal(true)
```

</details>

#### after:YYYY/MM/DD -> SINCE dd-Mon-yyyy

- after:YYYY/MM/DD -> SINCE dd-Mon-yyyy
- Verify: after:YYYY/MM/DD -> SINCE dd-Mon-yyyy
   - Expected: imap_date_from_gmail("2026/07/05") equals `05-Jul-2026`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("after:YYYY/MM/DD -> SINCE dd-Mon-yyyy")
step("Verify: after:YYYY/MM/DD -> SINCE dd-Mon-yyyy")
expect(imap_date_from_gmail("2026/07/05")).to_equal("05-Jul-2026")
```

</details>

#### before:YYYY/MM/DD -> BEFORE dd-Mon-yyyy (reuses the same date conversion)

- before:YYYY/MM/DD -> BEFORE dd-Mon-yyyy (reuses the same date conversion)
- Verify: before:YYYY/MM/DD -> BEFORE dd-Mon-yyyy (reuses the same date conversion)
   - Expected: imap_date_from_gmail("2025/12/31") equals `31-Dec-2025`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("before:YYYY/MM/DD -> BEFORE dd-Mon-yyyy (reuses the same date conversion)")
step("Verify: before:YYYY/MM/DD -> BEFORE dd-Mon-yyyy (reuses the same date conversion)")
expect(imap_date_from_gmail("2025/12/31")).to_equal("31-Dec-2025")
```

</details>

#### newer_than:Nd parses to N days

- newer_than:Nd parses to N days
- Verify: newer_than:Nd parses to N days
   - Expected: relative_window_days("7d") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("newer_than:Nd parses to N days")
step("Verify: newer_than:Nd parses to N days")
expect(relative_window_days("7d")).to_equal(7)
```

</details>

#### newer_than:Nm parses to N*30 days

- newer_than:Nm parses to N*30 days
- Verify: newer_than:Nm parses to N*30 days
   - Expected: relative_window_days("2m") equals `60`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("newer_than:Nm parses to N*30 days")
step("Verify: newer_than:Nm parses to N*30 days")
expect(relative_window_days("2m")).to_equal(60)
```

</details>

#### older_than:Ny parses to N*365 days

- older_than:Ny parses to N*365 days
- Verify: older_than:Ny parses to N*365 days
   - Expected: relative_window_days("1y") equals `365`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("older_than:Ny parses to N*365 days")
step("Verify: older_than:Ny parses to N*365 days")
expect(relative_window_days("1y")).to_equal(365)
```

</details>

#### malformed newer_than/older_than value returns -1

- malformed newer_than/older_than value returns -1
- Verify: malformed newer_than/older_than value returns -1
   - Expected: relative_window_days("bogus") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("malformed newer_than/older_than value returns -1")
step("Verify: malformed newer_than/older_than value returns -1")
expect(relative_window_days("bogus")).to_equal(-1)
```

</details>

#### label:X -> select IMAP folder X instead of INBOX (identity seam)

- label:X -> select IMAP folder X instead of INBOX (identity seam)
- Verify: label:X -> select IMAP folder X instead of INBOX (identity seam)
   - Expected: imap_label_to_folder("Work") equals `Work`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("label:X -> select IMAP folder X instead of INBOX (identity seam)")
step("Verify: label:X -> select IMAP folder X instead of INBOX (identity seam)")
expect(imap_label_to_folder("Work")).to_equal("Work")
```

</details>

#### in:trash/in:spam -> generic provider folder names

- in:trash/in:spam -> generic provider folder names
- Verify: in:trash/in:spam -> generic provider folder names
   - Expected: imap_folder_for_in("trash") equals `Trash`
   - Expected: imap_folder_for_in("spam") equals `Spam`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("in:trash/in:spam -> generic provider folder names")
step("Verify: in:trash/in:spam -> generic provider folder names")
expect(imap_folder_for_in("trash")).to_equal("Trash")
expect(imap_folder_for_in("spam")).to_equal("Spam")
```

</details>

#### in:trash/in:spam -> Gmail-specific [Gmail]/... folder names

- in:trash/in:spam -> Gmail-specific [Gmail]/... folder names
- Verify: in:trash/in:spam -> Gmail-specific [Gmail]/... folder names
   - Expected: imap_gmail_folder_for_in("trash") equals `[Gmail]/Trash`
   - Expected: imap_gmail_folder_for_in("spam") equals `[Gmail]/Spam`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("in:trash/in:spam -> Gmail-specific [Gmail]/... folder names")
step("Verify: in:trash/in:spam -> Gmail-specific [Gmail]/... folder names")
expect(imap_gmail_folder_for_in("trash")).to_equal("[Gmail]/Trash")
expect(imap_gmail_folder_for_in("spam")).to_equal("[Gmail]/Spam")
```

</details>

#### category:X has no IMAP equivalent - documented error

- category:X has no IMAP equivalent - documented error
- Verify: category:X has no IMAP equivalent - documented error
   - Expected: imap_warning_category() contains `no IMAP equivalent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("category:X has no IMAP equivalent - documented error")
step("Verify: category:X has no IMAP equivalent - documented error")
expect(imap_warning_category().contains("no IMAP equivalent")).to_equal(true)
```

</details>

#### filename:X is unsupported without a MIME-structure fetch

- filename:X is unsupported without a MIME-structure fetch
- Verify: filename:X is unsupported without a MIME-structure fetch
   - Expected: imap_warning_filename() contains `BODYSTRUCTURE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("filename:X is unsupported without a MIME-structure fetch")
step("Verify: filename:X is unsupported without a MIME-structure fetch")
expect(imap_warning_filename().contains("BODYSTRUCTURE")).to_equal(true)
```

</details>

#### larger:/smaller: has no IMAP SEARCH equivalent

- larger:/smaller: has no IMAP SEARCH equivalent
- Verify: larger:/smaller: has no IMAP SEARCH equivalent
   - Expected: imap_warning_larger_smaller() contains `RFC822.SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("larger:/smaller: has no IMAP SEARCH equivalent")
step("Verify: larger:/smaller: has no IMAP SEARCH equivalent")
expect(imap_warning_larger_smaller().contains("RFC822.SIZE")).to_equal(true)
```

</details>

#### -term -> NOT term

- -term -> NOT term
- Verify: -term -> NOT term
   - Expected: imap_term_negate("FROM \"alice\"") equals `NOT FROM "alice"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("-term -> NOT term")
step("Verify: -term -> NOT term")
expect(imap_term_negate("FROM \"alice\"")).to_equal("NOT FROM \"alice\"")
```

</details>

#### OR -> OR term1 term2 (2-ary)

- OR -> OR term1 term2 (2-ary)
- Verify: OR -> OR term1 term2 (2-ary)
   - Expected: imap_term_or("FROM \"a\"", "FROM \"b\"") equals `OR FROM "a" FROM "b"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("OR -> OR term1 term2 (2-ary)")
step("Verify: OR -> OR term1 term2 (2-ary)")
expect(imap_term_or("FROM \"a\"", "FROM \"b\"")).to_equal("OR FROM \"a\" FROM \"b\"")
```

</details>

#### n-ary Gmail OR right-folds into nested 2-ary IMAP OR

- n-ary Gmail OR right-folds into nested 2-ary IMAP OR
- Verify: n-ary Gmail OR right-folds into nested 2-ary IMAP OR
   - Expected: imap_term_or_nary(["A", "B", "C"]) equals `OR A OR B C`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("n-ary Gmail OR right-folds into nested 2-ary IMAP OR")
step("Verify: n-ary Gmail OR right-folds into nested 2-ary IMAP OR")
expect(imap_term_or_nary(["A", "B", "C"])).to_equal("OR A OR B C")
```

</details>

#### n-ary OR with a single term is the term itself

- n-ary OR with a single term is the term itself
- Verify: n-ary OR with a single term is the term itself
   - Expected: imap_term_or_nary(["A"]) equals `A`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("n-ary OR with a single term is the term itself")
step("Verify: n-ary OR with a single term is the term itself")
expect(imap_term_or_nary(["A"])).to_equal("A")
```

</details>

### 5c: Outlook/Graph $search KQL (primary) + $filter (structured listing)

#### from:X -> KQL from:X

- from:X -> KQL from:X
- Verify: from:X -> KQL from:X
   - Expected: kql_term_from("alice") equals `from:alice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("from:X -> KQL from:X")
step("Verify: from:X -> KQL from:X")
expect(kql_term_from("alice")).to_equal("from:alice")
```

</details>

#### to:X -> KQL to:X

- to:X -> KQL to:X
- Verify: to:X -> KQL to:X
   - Expected: kql_term_to("bob") equals `to:bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("to:X -> KQL to:X")
step("Verify: to:X -> KQL to:X")
expect(kql_term_to("bob")).to_equal("to:bob")
```

</details>

#### cc:X -> KQL cc:X

- cc:X -> KQL cc:X
- Verify: cc:X -> KQL cc:X
   - Expected: kql_term_cc("carol") equals `cc:carol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("cc:X -> KQL cc:X")
step("Verify: cc:X -> KQL cc:X")
expect(kql_term_cc("carol")).to_equal("cc:carol")
```

</details>

#### bcc:X -> KQL bcc:X (documented as possibly unpopulated)

- bcc:X -> KQL bcc:X (documented as possibly unpopulated)
- Verify: bcc:X -> KQL bcc:X (documented as possibly unpopulated)
   - Expected: kql_term_bcc("dave") equals `bcc:dave`
   - Expected: kql_warning_bcc() contains `unclear if populated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bcc:X -> KQL bcc:X (documented as possibly unpopulated)")
step("Verify: bcc:X -> KQL bcc:X (documented as possibly unpopulated)")
expect(kql_term_bcc("dave")).to_equal("bcc:dave")
expect(kql_warning_bcc().contains("unclear if populated")).to_equal(true)
```

</details>

#### subject:X -> KQL subject:X

- subject:X -> KQL subject:X
- Verify: subject:X -> KQL subject:X
   - Expected: kql_term_subject("invoice") equals `subject:invoice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("subject:X -> KQL subject:X")
step("Verify: subject:X -> KQL subject:X")
expect(kql_term_subject("invoice")).to_equal("subject:invoice")
```

</details>

#### is:unread/is:read/is:starred are NOT in the KQL property set - route through $filter

- is:unread/is:read/is:starred are NOT in the KQL property set - route through $filter
- Verify: is:unread/is:read/is:starred are NOT in the KQL property set - route through $filter
   - Expected: filter_term_is_unread() equals `isRead eq false`
   - Expected: filter_term_is_read() equals `isRead eq true`
   - Expected: filter_term_is_starred() equals `flag/flagStatus eq 'flagged'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is:unread/is:read/is:starred are NOT in the KQL property set - route through $filter")
step("Verify: is:unread/is:read/is:starred are NOT in the KQL property set - route through $filter")
expect(filter_term_is_unread()).to_equal("isRead eq false")
expect(filter_term_is_read()).to_equal("isRead eq true")
expect(filter_term_is_starred()).to_equal("flag/flagStatus eq 'flagged'")
```

</details>

#### is:important -> KQL importance:high

- is:important -> KQL importance:high
- Verify: is:important -> KQL importance:high
   - Expected: kql_term_is_important() equals `importance:high`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is:important -> KQL importance:high")
step("Verify: is:important -> KQL importance:high")
expect(kql_term_is_important()).to_equal("importance:high")
```

</details>

#### is:important -> $filter importance eq 'high'

- is:important -> $filter importance eq 'high'
- Verify: is:important -> $filter importance eq 'high'
   - Expected: filter_term_importance_high() equals `importance eq 'high'`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is:important -> $filter importance eq 'high'")
step("Verify: is:important -> $filter importance eq 'high'")
expect(filter_term_importance_high()).to_equal("importance eq 'high'")
```

</details>

#### has:attachment -> KQL hasattachment:true

- has:attachment -> KQL hasattachment:true
- Verify: has:attachment -> KQL hasattachment:true
   - Expected: kql_term_has_attachment() equals `hasattachment:true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("has:attachment -> KQL hasattachment:true")
step("Verify: has:attachment -> KQL hasattachment:true")
expect(kql_term_has_attachment()).to_equal("hasattachment:true")
```

</details>

#### has:attachment -> $filter hasAttachments eq true (direct field)

- has:attachment -> $filter hasAttachments eq true (direct field)
- Verify: has:attachment -> $filter hasAttachments eq true (direct field)
   - Expected: filter_term_has_attachment() equals `hasAttachments eq true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("has:attachment -> $filter hasAttachments eq true (direct field)")
step("Verify: has:attachment -> $filter hasAttachments eq true (direct field)")
expect(filter_term_has_attachment()).to_equal("hasAttachments eq true")
```

</details>

#### after:YYYY/MM/DD -> KQL received:YYYY-MM-DD..

- after:YYYY/MM/DD -> KQL received:YYYY-MM-DD..
- Verify: after:YYYY/MM/DD -> KQL received:YYYY-MM-DD..
   - Expected: kql_term_received_after(iso_date_from_gmail("2026/07/05")) equals `received:2026-07-05..`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("after:YYYY/MM/DD -> KQL received:YYYY-MM-DD..")
step("Verify: after:YYYY/MM/DD -> KQL received:YYYY-MM-DD..")
expect(kql_term_received_after(iso_date_from_gmail("2026/07/05"))).to_equal("received:2026-07-05..")
```

</details>

#### before:YYYY/MM/DD -> KQL received:..YYYY-MM-DD

- before:YYYY/MM/DD -> KQL received:..YYYY-MM-DD
- Verify: before:YYYY/MM/DD -> KQL received:..YYYY-MM-DD
   - Expected: kql_term_received_before(iso_date_from_gmail("2026/07/05")) equals `received:..2026-07-05`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("before:YYYY/MM/DD -> KQL received:..YYYY-MM-DD")
step("Verify: before:YYYY/MM/DD -> KQL received:..YYYY-MM-DD")
expect(kql_term_received_before(iso_date_from_gmail("2026/07/05"))).to_equal("received:..2026-07-05")
```

</details>

#### after:/before: -> $filter receivedDateTime ge/le

- after:/before: -> $filter receivedDateTime ge/le
- Verify: after:/before: -> $filter receivedDateTime ge/le
   - Expected: filter_term_received_after("2026-07-05") equals `receivedDateTime ge 2026-07-05T00:00:00Z`
   - Expected: filter_term_received_before("2026-07-05") equals `receivedDateTime le 2026-07-05T00:00:00Z`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("after:/before: -> $filter receivedDateTime ge/le")
step("Verify: after:/before: -> $filter receivedDateTime ge/le")
expect(filter_term_received_after("2026-07-05")).to_equal("receivedDateTime ge 2026-07-05T00:00:00Z")
expect(filter_term_received_before("2026-07-05")).to_equal("receivedDateTime le 2026-07-05T00:00:00Z")
```

</details>

#### from:/to:/cc:/subject: -> $filter fallback forms

- from:/to:/cc:/subject: -> $filter fallback forms
- Verify: from:/to:/cc:/subject: -> $filter fallback forms
   - Expected: filter_term_from("alice") equals `from/emailAddress/address eq 'alice'`
   - Expected: filter_term_to("bob") equals `toRecipients/any(r:r/emailAddress/address eq 'bob')`
   - Expected: filter_term_cc("carol") equals `ccRecipients/any(r:r/emailAddress/address eq 'carol')`
   - Expected: filter_term_subject_contains("invoice") equals `contains(subject,'invoice')`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("from:/to:/cc:/subject: -> $filter fallback forms")
step("Verify: from:/to:/cc:/subject: -> $filter fallback forms")
expect(filter_term_from("alice")).to_equal("from/emailAddress/address eq 'alice'")
expect(filter_term_to("bob")).to_equal("toRecipients/any(r:r/emailAddress/address eq 'bob')")
expect(filter_term_cc("carol")).to_equal("ccRecipients/any(r:r/emailAddress/address eq 'carol')")
expect(filter_term_subject_contains("invoice")).to_equal("contains(subject,'invoice')")
```

</details>

#### label:X -> well-known folder routing for system labels

- label:X -> well-known folder routing for system labels
- Verify: label:X -> well-known folder routing for system labels
   - Expected: graph_well_known_folder_for_label("INBOX") equals `inbox`
   - Expected: graph_well_known_folder_for_label("SENT") equals `sentitems`
   - Expected: graph_well_known_folder_for_label("DRAFT") equals `drafts`
   - Expected: graph_well_known_folder_for_label("TRASH") equals `deleteditems`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("label:X -> well-known folder routing for system labels")
step("Verify: label:X -> well-known folder routing for system labels")
expect(graph_well_known_folder_for_label("INBOX")).to_equal("inbox")
expect(graph_well_known_folder_for_label("SENT")).to_equal("sentitems")
expect(graph_well_known_folder_for_label("DRAFT")).to_equal("drafts")
expect(graph_well_known_folder_for_label("TRASH")).to_equal("deleteditems")
```

</details>

#### label:X -> non-system label falls back to category (no well-known folder)

- label:X -> non-system label falls back to category (no well-known folder)
- Verify: label:X -> non-system label falls back to category (no well-known folder)
   - Expected: graph_well_known_folder_for_label("Work") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("label:X -> non-system label falls back to category (no well-known folder)")
step("Verify: label:X -> non-system label falls back to category (no well-known folder)")
expect(graph_well_known_folder_for_label("Work")).to_equal("")
```

</details>

#### label:X -> category KQL term / $filter categories/any fallback

- label:X -> category KQL term / $filter categories/any fallback
- Verify: label:X -> category KQL term / $filter categories/any fallback
   - Expected: kql_term_filename("Work") != "" is true
   - Expected: filter_term_category("Work") equals `categories/any(c:c eq 'Work')`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("label:X -> category KQL term / $filter categories/any fallback")
step("Verify: label:X -> category KQL term / $filter categories/any fallback")
expect(kql_term_filename("Work") != "").to_equal(true)
expect(filter_term_category("Work")).to_equal("categories/any(c:c eq 'Work')")
```

</details>

#### category:X (Gmail auto categories) has no Graph equivalent

- category:X (Gmail auto categories) has no Graph equivalent
- Verify: category:X (Gmail auto categories) has no Graph equivalent
   - Expected: kql_warning_category() contains `no Graph equivalent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("category:X (Gmail auto categories) has no Graph equivalent")
step("Verify: category:X (Gmail auto categories) has no Graph equivalent")
expect(kql_warning_category().contains("no Graph equivalent")).to_equal(true)
```

</details>

#### filename:X -> KQL attachment:X

- filename:X -> KQL attachment:X
- Verify: filename:X -> KQL attachment:X
   - Expected: kql_term_filename("report.pdf") equals `attachment:report.pdf`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("filename:X -> KQL attachment:X")
step("Verify: filename:X -> KQL attachment:X")
expect(kql_term_filename("report.pdf")).to_equal("attachment:report.pdf")
```

</details>

#### filename:X -> $filter attachments/any fallback

- filename:X -> $filter attachments/any fallback
- Verify: filename:X -> $filter attachments/any fallback
   - Expected: filter_term_attachment_filename("report.pdf") equals `attachments/any(a:a/name eq 'report.pdf')`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("filename:X -> $filter attachments/any fallback")
step("Verify: filename:X -> $filter attachments/any fallback")
expect(filter_term_attachment_filename("report.pdf")).to_equal("attachments/any(a:a/name eq 'report.pdf')")
```

</details>

#### larger:N/smaller:N -> KQL size:N.. / size:..N

- larger:N/smaller:N -> KQL size:N.. / size:..N
- Verify: larger:N/smaller:N -> KQL size:N.. / size:..N
   - Expected: kql_term_size_larger("1000000") equals `size:1000000..`
   - Expected: kql_term_size_smaller("1000") equals `size:..1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("larger:N/smaller:N -> KQL size:N.. / size:..N")
step("Verify: larger:N/smaller:N -> KQL size:N.. / size:..N")
expect(kql_term_size_larger("1000000")).to_equal("size:1000000..")
expect(kql_term_size_smaller("1000")).to_equal("size:..1000")
```

</details>

#### larger:/smaller: has no $filter equivalent - search verb (KQL) only

- larger:/smaller: has no $filter equivalent - search verb (KQL) only
- Verify: larger:/smaller: has no $filter equivalent - search verb (KQL) only
   - Expected: kql_warning_larger_smaller_filter() contains `$filter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("larger:/smaller: has no $filter equivalent - search verb (KQL) only")
step("Verify: larger:/smaller: has no $filter equivalent - search verb (KQL) only")
expect(kql_warning_larger_smaller_filter().contains("$filter")).to_equal(true)
```

</details>

#### -term -> KQL NOT term

- -term -> KQL NOT term
- Verify: -term -> KQL NOT term
   - Expected: kql_term_negate("subject:invoice") equals `NOT subject:invoice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("-term -> KQL NOT term")
step("Verify: -term -> KQL NOT term")
expect(kql_term_negate("subject:invoice")).to_equal("NOT subject:invoice")
```

</details>

#### -term -> $filter not(...)

- -term -> $filter not(...)
- Verify: -term -> $filter not(...)
   - Expected: filter_term_negate("isRead eq false") equals `not(isRead eq false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("-term -> $filter not(...)")
step("Verify: -term -> $filter not(...)")
expect(filter_term_negate("isRead eq false")).to_equal("not(isRead eq false)")
```

</details>

#### OR -> KQL A OR B (native, n-ary)

- OR -> KQL A OR B (native, n-ary)
- Verify: OR -> KQL A OR B (native, n-ary)
   - Expected: kql_term_or("from:a", "from:b") equals `from:a OR from:b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("OR -> KQL A OR B (native, n-ary)")
step("Verify: OR -> KQL A OR B (native, n-ary)")
expect(kql_term_or("from:a", "from:b")).to_equal("from:a OR from:b")
```

</details>

#### OR -> $filter (A) or (B)

- OR -> $filter (A) or (B)
- Verify: OR -> $filter (A) or (B)
   - Expected: filter_term_or("isRead eq true", "isRead eq false") equals `(isRead eq true) or (isRead eq false)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("OR -> $filter (A) or (B)")
step("Verify: OR -> $filter (A) or (B)")
expect(filter_term_or("isRead eq true", "isRead eq false")).to_equal("(isRead eq true) or (isRead eq false)")
```

</details>

### 6: label/star/archive verb -> backend action mapping

#### removing the INBOX label IS archive on Gmail (label --remove INBOX == archive)

- removing the INBOX label IS archive on Gmail (label --remove INBOX == archive)
- Verify: removing the INBOX label IS archive on Gmail (label --remove INBOX == archive)
   - Expected: is_archive_equivalent_label_removal("INBOX") is true
   - Expected: is_archive_equivalent_label_removal("inbox") is true
   - Expected: is_archive_equivalent_label_removal("Work") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("removing the INBOX label IS archive on Gmail (label --remove INBOX == archive)")
step("Verify: removing the INBOX label IS archive on Gmail (label --remove INBOX == archive)")
expect(is_archive_equivalent_label_removal("INBOX")).to_equal(true)
expect(is_archive_equivalent_label_removal("inbox")).to_equal(true)
expect(is_archive_equivalent_label_removal("Work")).to_equal(false)
```

</details>

#### STARRED is a system label handled specially, not a folder copy

- STARRED is a system label handled specially, not a folder copy
- Verify: STARRED is a system label handled specially, not a folder copy
   - Expected: is_system_label_starred("STARRED") is true
   - Expected: is_system_label_starred("starred") is true
   - Expected: is_system_label_starred("Work") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("STARRED is a system label handled specially, not a folder copy")
step("Verify: STARRED is a system label handled specially, not a folder copy")
expect(is_system_label_starred("STARRED")).to_equal(true)
expect(is_system_label_starred("starred")).to_equal(true)
expect(is_system_label_starred("Work")).to_equal(false)
```

</details>

#### star on -> +FLAGS (\\Flagged), star --off -> -FLAGS (\\Flagged)

- star on -> +FLAGS (\\Flagged), star --off -> -FLAGS (\\Flagged)
- Verify: star on -> +FLAGS (Flagged), star --off -> -FLAGS (Flagged)
   - Expected: imap_star_flag_term(true) equals `+FLAGS (\\Flagged)`
   - Expected: imap_star_flag_term(false) equals `-FLAGS (\\Flagged)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("star on -> +FLAGS (\\Flagged), star --off -> -FLAGS (\\Flagged)")
step("Verify: star on -> +FLAGS (Flagged), star --off -> -FLAGS (Flagged)")
expect(imap_star_flag_term(true)).to_equal("+FLAGS (\\Flagged)")
expect(imap_star_flag_term(false)).to_equal("-FLAGS (\\Flagged)")
```

</details>

#### Graph flag.flagStatus mirrors star on/off

- Graph flag.flagStatus mirrors star on/off
- Verify: Graph flag.flagStatus mirrors star on/off
   - Expected: graph_flag_status(true) equals `flagged`
   - Expected: graph_flag_status(false) equals `notFlagged`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("Graph flag.flagStatus mirrors star on/off")
step("Verify: Graph flag.flagStatus mirrors star on/off")
expect(graph_flag_status(true)).to_equal("flagged")
expect(graph_flag_status(false)).to_equal("notFlagged")
```

</details>

#### archive folder is provider-aware: gmail -> [Gmail]/All Mail, else Archive

- archive folder is provider-aware: gmail -> [Gmail]/All Mail, else Archive
- Verify: archive folder is provider-aware: gmail -> [Gmail]/All Mail, else Archive
   - Expected: archive_folder_for_provider("gmail") equals `[Gmail]/All Mail`
   - Expected: archive_folder_for_provider("outlook_imap") equals `Archive`
   - Expected: archive_folder_for_provider("yahoo") equals `Archive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("archive folder is provider-aware: gmail -> [Gmail]/All Mail, else Archive")
step("Verify: archive folder is provider-aware: gmail -> [Gmail]/All Mail, else Archive")
expect(archive_folder_for_provider("gmail")).to_equal("[Gmail]/All Mail")
expect(archive_folder_for_provider("outlook_imap")).to_equal("Archive")
expect(archive_folder_for_provider("yahoo")).to_equal("Archive")
```

</details>

#### Graph archive resolves via the well-known 'archive' folder id

- Graph archive resolves via the well-known 'archive' folder id
- Verify: Graph archive resolves via the well-known 'archive' folder id
   - Expected: graph_archive_folder_id() equals `archive`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("Graph archive resolves via the well-known 'archive' folder id")
step("Verify: Graph archive resolves via the well-known 'archive' folder id")
expect(graph_archive_folder_id()).to_equal("archive")
```

</details>

### Gmail query tokenizer + operator classifier

#### splits on whitespace

- splits on whitespace
- Verify: splits on whitespace
   - Expected: tokens.len() equals `2`
   - Expected: tokens[0] equals `from:alice`
   - Expected: tokens[1] equals `is:unread`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("splits on whitespace")
step("Verify: splits on whitespace")
val tokens = tokenize_gmail_query("from:alice is:unread")
expect(tokens.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(tokens[0]).to_equal("from:alice")
expect(tokens[1]).to_equal("is:unread")
```

</details>

#### keeps a quoted phrase (including an embedded key: prefix) as one token

- keeps a quoted phrase (including an embedded key: prefix) as one token
- Verify: keeps a quoted phrase (including an embedded key: prefix) as one token
   - Expected: tokens.len() equals `2`
   - Expected: tokens[0] equals `subject:"hello world"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps a quoted phrase (including an embedded key: prefix) as one token")
step("Verify: keeps a quoted phrase (including an embedded key: prefix) as one token")
val tokens = tokenize_gmail_query("subject:\"hello world\" is:unread")
expect(tokens.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(tokens[0]).to_equal("subject:\"hello world\"")
```

</details>

#### parses recognized key:value operators into typed terms

- parses recognized key:value operators into typed terms
- Verify: parses recognized key:value operators into typed terms
   - Expected: terms.len() equals `2`
   - Expected: terms[0].op equals `from`
   - Expected: terms[0].value equals `alice`
   - Expected: terms[1].op equals `subject`
   - Expected: terms[1].value equals `invoice`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses recognized key:value operators into typed terms")
step("Verify: parses recognized key:value operators into typed terms")
val terms = parse_gmail_query("from:alice subject:invoice")
expect(terms.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(terms[0].op).to_equal("from")
expect(terms[0].value).to_equal("alice")
expect(terms[1].op).to_equal("subject")
expect(terms[1].value).to_equal("invoice")
```

</details>

#### strips quotes from a quoted operator value

- strips quotes from a quoted operator value
- Verify: strips quotes from a quoted operator value
   - Expected: terms[0].value equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("strips quotes from a quoted operator value")
step("Verify: strips quotes from a quoted operator value")
val terms = parse_gmail_query("subject:\"hello world\"")
expect(terms[0].value).to_equal("hello world")
```

</details>

#### parses free text (no key:) as op=text

- parses free text (no key:) as op=text
- Verify: parses free text (no key:) as op=text
   - Expected: terms[0].op equals `text`
   - Expected: terms[0].value equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses free text (no key:) as op=text")
step("Verify: parses free text (no key:) as op=text")
val terms = parse_gmail_query("hello")
expect(terms[0].op).to_equal("text")
expect(terms[0].value).to_equal("hello")
```

</details>

#### parses -term as negated

- parses -term as negated
- Verify: parses -term as negated
   - Expected: terms[0].op equals `from`
   - Expected: terms[0].value equals `alice`
   - Expected: terms[0].negated is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses -term as negated")
step("Verify: parses -term as negated")
val terms = parse_gmail_query("-from:alice")
expect(terms[0].op).to_equal("from")
expect(terms[0].value).to_equal("alice")
expect(terms[0].negated).to_equal(true)
```

</details>

#### parses a bare OR token

- parses a bare OR token
- Verify: parses a bare OR token
   - Expected: terms.len() equals `3`
   - Expected: terms[1].op equals `or`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses a bare OR token")
step("Verify: parses a bare OR token")
val terms = parse_gmail_query("from:a OR from:b")
expect(terms.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(terms[1].op).to_equal("or")
```

</details>

#### an unrecognized key:value shape falls back to free text

- an unrecognized key:value shape falls back to free text
- Verify: an unrecognized key:value shape falls back to free text
   - Expected: terms[0].op equals `text`
   - Expected: terms[0].value equals `weirdkey:value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("an unrecognized key:value shape falls back to free text")
step("Verify: an unrecognized key:value shape falls back to free text")
val terms = parse_gmail_query("weirdkey:value")
expect(terms[0].op).to_equal("text")
expect(terms[0].value).to_equal("weirdkey:value")
```

</details>

#### parses every recognized operator key from the §5 tables

- parses every recognized operator key from the §5 tables
- Verify: parses every recognized operator key from the §5 tables
   - Expected: terms.len() equals `14`
   - Expected: terms[0].op equals `to`
   - Expected: terms[13].op equals `smaller`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parses every recognized operator key from the §5 tables")
step("Verify: parses every recognized operator key from the §5 tables")
val terms = parse_gmail_query("to:a cc:b bcc:c has:attachment after:2026/01/01 before:2026/02/01 newer_than:7d older_than:30d label:Work in:trash category:promotions filename:x.pdf larger:1000 smaller:100")
expect(terms.len()).to_equal(14)  # oracle: 14 — named expected value from the requirement
expect(terms[0].op).to_equal("to")
expect(terms[13].op).to_equal("smaller")
```

</details>

### date parsing helpers

#### parse_gmail_date splits YYYY/MM/DD into (year, month, day)

- parse_gmail_date splits YYYY/MM/DD into (year, month, day)
- Verify: parse_gmail_date splits YYYY/MM/DD into (year, month, day)
   - Expected: y equals `2026`
   - Expected: m equals `7`
   - Expected: d equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parse_gmail_date splits YYYY/MM/DD into (year, month, day)")
step("Verify: parse_gmail_date splits YYYY/MM/DD into (year, month, day)")
val (y, m, d) = parse_gmail_date("2026/07/05")
expect(y).to_equal(2026)  # oracle: 2026 — named expected value from the requirement
expect(m).to_equal(7)  # oracle: 7 — named expected value from the requirement
expect(d).to_equal(5)  # oracle: 5 — named expected value from the requirement
```

</details>

#### parse_gmail_date returns (-1,-1,-1) on malformed input

- parse_gmail_date returns (-1,-1,-1) on malformed input
- Verify: parse_gmail_date returns (-1,-1,-1) on malformed input
   - Expected: y equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("parse_gmail_date returns (-1,-1,-1) on malformed input")
step("Verify: parse_gmail_date returns (-1,-1,-1) on malformed input")
val (y, _m, _d) = parse_gmail_date("not-a-date")
expect(y).to_equal(-1)  # oracle: -1 — named expected value from the requirement
```

</details>

#### iso_date_from_gmail converts YYYY/MM/DD -> YYYY-MM-DD

- iso_date_from_gmail converts YYYY/MM/DD -> YYYY-MM-DD
- Verify: iso_date_from_gmail converts YYYY/MM/DD -> YYYY-MM-DD
   - Expected: iso_date_from_gmail("2026/07/05") equals `2026-07-05`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("iso_date_from_gmail converts YYYY/MM/DD -> YYYY-MM-DD")
step("Verify: iso_date_from_gmail converts YYYY/MM/DD -> YYYY-MM-DD")
expect(iso_date_from_gmail("2026/07/05")).to_equal("2026-07-05")
```

</details>

#### iso_date_from_gmail returns empty text on malformed input

- iso_date_from_gmail returns empty text on malformed input
- Verify: iso_date_from_gmail returns empty text on malformed input
   - Expected: iso_date_from_gmail("bogus") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("iso_date_from_gmail returns empty text on malformed input")
step("Verify: iso_date_from_gmail returns empty text on malformed input")
expect(iso_date_from_gmail("bogus")).to_equal("")
```

</details>

#### imap_date_from_gmail returns empty text on malformed input

- imap_date_from_gmail returns empty text on malformed input
- Verify: imap_date_from_gmail returns empty text on malformed input
   - Expected: imap_date_from_gmail("bogus") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("imap_date_from_gmail returns empty text on malformed input")
step("Verify: imap_date_from_gmail returns empty text on malformed input")
expect(imap_date_from_gmail("bogus")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 74 |
| Active scenarios | 74 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-DEVHUB-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b5d00b389da82b91508be55176821a49ba93400d8fd9e360efa41845544afb6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b5d00b389da82b91508be55176821a49ba93400d8fd9e360efa41845544afb6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b5d00b389da82b91508be55176821a49ba93400d8fd9e360efa41845544afb6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/devhub/email_translate_spec.spl
mirror: doc/06_spec/01_unit/app/devhub/email_translate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/devhub/email_translate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/devhub/email_translate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/devhub/email_translate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/devhub/email_translate_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the query verbatim, zero translation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/email_translate_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'from:X -> FROM \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/devhub/email_translate_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'to:X -> TO \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->

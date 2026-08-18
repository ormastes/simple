# mail_rules_spec

> Mail rules engine spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mail_rules_spec

Mail rules engine spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/mail_rules_spec.spl` |
| Updated | 2026-08-18 |
| Generator | `simple spipe-docgen` (Simple) |

Mail rules engine spec.

Outlook-style rules at the pure model level: case-insensitive field matching,
first-matching-rule-wins application (move / flag / markread), a plain-text
rule parser, and the macro API wrapper. All expectations hand-computed from a
fixed four-email mailbox.

## Scenarios

### mail rules: matching
_rule_matches is a case-insensitive substring test on the chosen field._

#### matches sender case-insensitively on the from field

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val emails = _mailbox()
val rule = _rule_from_alex()
val e1 = emails[0]
val e2 = emails[1]
assert_true(rule_matches(rule, e1))
assert_false(rule_matches(rule, e2))
```

</details>

#### matches the subject field and reports both hits on the double-match email

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val emails = _mailbox()
val rule_a = _rule_from_alex()
val rule_b = _rule_urgent()
val e2 = emails[1]
val e3 = emails[2]
val e4 = emails[3]
assert_true(rule_matches(rule_b, e2))
assert_true(rule_matches(rule_a, e3))
assert_true(rule_matches(rule_b, e3))
assert_false(rule_matches(rule_a, e4))
assert_false(rule_matches(rule_b, e4))
```

</details>

#### matches on the body field and never on an empty needle

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val emails = _mailbox()
val body_rule = MailRule(name: "InvoiceBody", field: "body", contains: "invoice 42", action: "markread", target: "")
val empty_rule = MailRule(name: "Empty", field: "subject", contains: "", action: "flag", target: "")
val e3 = emails[2]
assert_true(rule_matches(body_rule, e3))
assert_false(rule_matches(empty_rule, e3))
```

</details>

### mail rules: application
_apply_rules is first-matching-rule-wins per email and returns a new list._

#### applies move and flag; first rule wins on the double match; no-match is untouched

<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val emails = _mailbox()
val rules = [_rule_from_alex(), _rule_urgent()]
val result = apply_rules(emails, rules)
expect(result.len()).to_equal(4)
val r1 = result[0]
val r2 = result[1]
val r3 = result[2]
val r4 = result[3]
# e1: FromAlex moved it to Archive, flags untouched
expect(r1.folder).to_equal("Archive")
assert_false(r1.starred)
assert_false(r1.read)
# e2: UrgentFlag starred it, folder untouched
expect(r2.folder).to_equal("Inbox")
assert_true(r2.starred)
# e3: matches both — FromAlex (first) wins: moved, NOT starred
expect(r3.folder).to_equal("Archive")
assert_false(r3.starred)
# e4: matches none — fully unchanged
expect(r4.folder).to_equal("Inbox")
assert_false(r4.starred)
assert_false(r4.read)
# copy semantics: the input list is not mutated
val orig1 = emails[0]
expect(orig1.folder).to_equal("Inbox")
```

</details>

#### markread sets the read flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val news = new_email("n1", _addr("News Bot", "news@example.com"), [_addr("Me", "me@simple.local")], "March digest", "Your monthly Newsletter digest is here.")
val rule = MailRule(name: "NewsRead", field: "body", contains: "newsletter", action: "markread", target: "")
val result = apply_rules([news], [rule])
val r1 = result[0]
assert_true(r1.read)
expect(r1.folder).to_equal("Inbox")
assert_false(r1.starred)
```

</details>

### mail rules: summary
_rules_summary counts, per rule, the emails it is the FIRST match for._

#### reports first-match counts per rule

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val emails = _mailbox()
val rules = [_rule_from_alex(), _rule_urgent()]
val lines = rules_summary(emails, rules)
expect(lines.len()).to_equal(2)
# FromAlex first-matches e1 and e3; UrgentFlag first-matches only e2
expect(lines[0]).to_equal("FromAlex: 2 matched")
expect(lines[1]).to_equal("UrgentFlag: 1 matched")
```

</details>

### mail rules: parser
_parse_rules reads one rule per line, skipping comments and blanks._

#### parses rules, strips quotes, and skips comments and blank lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val txt = "# archive alex\n\nFromAlex | from contains \"alex\" | move Archive\nFlagUrgent | subject contains urgent | flag\n"
val rules = parse_rules(txt)
expect(rules.len()).to_equal(2)
val r0 = rules[0]
val r1 = rules[1]
expect(r0.name).to_equal("FromAlex")
expect(r0.field).to_equal("from")
expect(r0.contains).to_equal("alex")
expect(r0.action).to_equal("move")
expect(r0.target).to_equal("Archive")
expect(r1.name).to_equal("FlagUrgent")
expect(r1.contains).to_equal("urgent")
expect(r1.action).to_equal("flag")
expect(r1.target).to_equal("")
```

</details>

#### keeps multi-word move targets and ignores malformed lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val txt = "OldStuff | subject contains \"2019\" | move Old Projects\nnot a rule line\nAlso | bad condition | flag"
val rules = parse_rules(txt)
expect(rules.len()).to_equal(1)
val r0 = rules[0]
expect(r0.target).to_equal("Old Projects")
expect(r0.contains).to_equal("2019")
```

</details>

### mail rules: macro API
_macro_mail_rules parses a rules spec and applies it in one call._

#### moves a matching email via the macro wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val emails = _mailbox()
val txt = "FromAlex | from contains \"alex\" | move Archive"
val result = macro_mail_rules(emails, txt)
val r1 = result[0]
val r2 = result[1]
expect(r1.folder).to_equal("Archive")
expect(r2.folder).to_equal("Inbox")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

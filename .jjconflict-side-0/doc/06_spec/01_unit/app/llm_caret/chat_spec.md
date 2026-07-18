# Chat Specification

> 1. chat clear

<!-- sdn-diagram:id=chat_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chat_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chat_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chat_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chat Specification

## Scenarios

### Chat History

#### starts empty

1. chat clear
   - Expected: chat_history_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
expect(chat_history_len()).to_equal(0)
```

</details>

#### adds user message

1. chat clear
2. chat add user
   - Expected: chat_history_len() equals `1`
   - Expected: chat_get_role(0) equals `user`
   - Expected: chat_get_content(0) equals `Hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_user("Hello")
expect(chat_history_len()).to_equal(1)
expect(chat_get_role(0)).to_equal("user")
expect(chat_get_content(0)).to_equal("Hello")
```

</details>

#### adds assistant message

1. chat clear
2. chat add assistant
   - Expected: chat_history_len() equals `1`
   - Expected: chat_get_role(0) equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_assistant("Hi there!")
expect(chat_history_len()).to_equal(1)
expect(chat_get_role(0)).to_equal("assistant")
```

</details>

#### maintains conversation order

1. chat clear
2. chat add user
3. chat add assistant
4. chat add user
   - Expected: chat_history_len() equals `3`
   - Expected: chat_get_role(0) equals `user`
   - Expected: chat_get_role(1) equals `assistant`
   - Expected: chat_get_role(2) equals `user`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_user("Hi")
chat_add_assistant("Hello!")
chat_add_user("How are you?")
expect(chat_history_len()).to_equal(3)
expect(chat_get_role(0)).to_equal("user")
expect(chat_get_role(1)).to_equal("assistant")
expect(chat_get_role(2)).to_equal("user")
```

</details>

#### clears history

1. chat clear
2. chat add user
3. chat clear
   - Expected: chat_history_len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_user("test")
chat_clear()
expect(chat_history_len()).to_equal(0)
```

</details>

#### returns empty for out-of-bounds index

1. chat clear
   - Expected: chat_get_role(-1) equals ``
   - Expected: chat_get_role(99) equals ``
   - Expected: chat_get_content(-1) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
expect(chat_get_role(-1)).to_equal("")
expect(chat_get_role(99)).to_equal("")
expect(chat_get_content(-1)).to_equal("")
```

</details>

### Chat Truncation

#### truncates to keep last N

1. chat clear
2. chat add user
3. chat add assistant
4. chat add user
5. chat add assistant
6. chat truncate
   - Expected: chat_history_len() equals `2`
   - Expected: chat_get_content(0) equals `msg2`
   - Expected: chat_get_content(1) equals `resp2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_user("msg1")
chat_add_assistant("resp1")
chat_add_user("msg2")
chat_add_assistant("resp2")
chat_truncate(2)
expect(chat_history_len()).to_equal(2)
expect(chat_get_content(0)).to_equal("msg2")
expect(chat_get_content(1)).to_equal("resp2")
```

</details>

#### does nothing when under limit

1. chat clear
2. chat add user
3. chat truncate
   - Expected: chat_history_len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_user("msg1")
chat_truncate(10)
expect(chat_history_len()).to_equal(1)
```

</details>

#### auto-truncates on max history

1. chat clear
2. chat set max history
3. chat add user
4. chat add assistant
5. chat add user
6. chat add assistant
   - Expected: chat_history_len() equals `3`
7. chat set max history


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_set_max_history(3)
chat_add_user("a")
chat_add_assistant("b")
chat_add_user("c")
chat_add_assistant("d")
expect(chat_history_len()).to_equal(3)
chat_set_max_history(100)
```

</details>

### Chat System Prompt

#### sets system prompt

1. chat set system prompt
   - Expected: chat_get_system_prompt() equals `Be helpful`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_set_system_prompt("Be helpful")
expect(chat_get_system_prompt()).to_equal("Be helpful")
```

</details>

#### can clear system prompt

1. chat set system prompt
   - Expected: chat_get_system_prompt() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_set_system_prompt("")
expect(chat_get_system_prompt()).to_equal("")
```

</details>

### Chat JSON

#### builds empty messages

1. chat clear
   - Expected: json equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
val json = chat_build_messages_json()
expect(json).to_equal("[]")
```

</details>

#### builds single message

1. chat clear
2. chat add user


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_user("Hello")
val json = chat_build_messages_json()
expect(json).to_contain("user")
expect(json).to_contain("Hello")
expect(json).to_start_with("[")
expect(json).to_end_with("]")
```

</details>

#### builds multi-turn conversation

1. chat clear
2. chat add user
3. chat add assistant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_user("Hi")
chat_add_assistant("Hello!")
val json = chat_build_messages_json()
expect(json).to_contain("user")
expect(json).to_contain("assistant")
```

</details>

### Chat Last Message

#### returns last content

1. chat clear
2. chat add user
3. chat add assistant
   - Expected: chat_last_content() equals `Second`
   - Expected: chat_last_role() equals `assistant`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
chat_add_user("First")
chat_add_assistant("Second")
expect(chat_last_content()).to_equal("Second")
expect(chat_last_role()).to_equal("assistant")
```

</details>

#### returns empty when no history

1. chat clear
   - Expected: chat_last_content() equals ``
   - Expected: chat_last_role() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
chat_clear()
expect(chat_last_content()).to_equal("")
expect(chat_last_role()).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/chat_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Chat History
- Chat Truncation
- Chat System Prompt
- Chat JSON
- Chat Last Message

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

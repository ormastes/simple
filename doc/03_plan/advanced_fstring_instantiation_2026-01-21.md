# Plan: Advanced Format String Instantiation

**Date:** 2026-01-21
**Status:** Planning

## Overview

Implement ergonomic format string instantiation with automatic const key validation:

```simple
val template = "Welcome {user} to {city}"
val result = template.with {"user": name, "city": location}
```

## Goals

1. **Auto-detection**: No explicit type annotations needed
2. **Compile-time validation**: Wrong/missing keys caught at compile time
3. **Short syntax**: Use `.with` method (not `.instantiate`)
4. **Natural flow**: Template defines contract, dict must satisfy it

## Design

### Syntax

```simple
# Define template - placeholders become const_keys automatically
val template = "Hello {name}, you have {count} messages"

# Instantiate with .with method
val result = template.with {"name": user_name, "count": msg_count}

# Returns formatted string: "Hello Alice, you have 5 messages"
```

### Type System

```
FString type carries const_keys metadata:
  template : FString<const_keys=["name", "count"]>

.with method signature:
  fn with(self: FString<K>, data: Dict<K, String>) -> String
  where K is the FString's const_keys
```

### Compile-Time Validation

| Case | Example | Error |
|------|---------|-------|
| Unknown key | `{"usr": x}` | "usr" not in ["user", "city"] |
| Missing key | `{"user": x}` | Missing required key "city" |
| All correct | `{"user": x, "city": y}` | OK |

## Implementation Phases

### Phase 1: FString Type Enhancement

1. Add `FStringType` to type checker with const_keys
2. FString inference returns `FStringType` instead of `Str`
3. Track const_keys in type metadata

**Files:**
- `src/rust/type/src/lib.rs` - Add `Type::FString { const_keys }`
- `src/rust/type/src/checker_infer.rs` - Return FStringType for FString expressions

### Phase 2: `.with` Method Implementation

1. Add `.with` as intrinsic method on FString type
2. Validate dict keys against FString's const_keys
3. Return String type

**Files:**
- `src/rust/type/src/checker_infer.rs` - Handle `.with` method call
- `src/rust/type/src/checker_check.rs` - Validate dict keys in method call

### Phase 3: Error Messages

1. Implement helpful error messages with suggestions
2. "Did you mean?" for typos
3. List expected keys in error

**Files:**
- `src/rust/type/src/lib.rs` - Enhance TypeError variants

### Phase 4: Runtime Implementation

1. Implement `FString.with()` in interpreter
2. Implement in codegen (Cranelift)

**Files:**
- `src/rust/runtime/src/value.rs` - FString.with runtime
- `src/rust/compiler/src/codegen/` - Codegen for .with

## API Design

```simple
# Core method
impl FString:
    fn with(data: Dict<Self.keys, String>) -> String:
        # Replace placeholders with values from dict
        ...

# Optional: Allow partial application
impl FString:
    fn partial(data: Dict<?, String>) -> FString:
        # Returns new FString with some placeholders filled
        ...
```

## Example Usage

```simple
# Email template
val email = """
Dear {recipient},

{body}

Best,
{sender}
"""

val formatted = email.with {
    "recipient": customer.name,
    "body": generate_body(),
    "sender": "Support Team"
}

# Config template
val url = "https://{host}:{port}/{path}"
val endpoint = url.with {"host": "api.example.com", "port": "443", "path": "v1/users"}

# Localization
val greeting = i18n("welcome_{lang}").with {"name": user.name}
```

## Testing Strategy

1. Unit tests for type inference
2. Unit tests for key validation
3. Integration tests for full flow
4. Error message tests

## Dependencies

- Phase 1 of const contract (FString const_keys extraction) - DONE
- Phase 2 of const contract (ConstKeySet type) - DONE
- Phase 3 of const contract (dependent keys resolution) - DONE

## Risks

1. **Breaking change?** No - `.with` is new method
2. **Performance** - Compile-time only, no runtime overhead
3. **Complexity** - Moderate, builds on existing infrastructure

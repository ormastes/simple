# Qualified Ignore Feature Design

## Overview

Add a new test state "qualified_ignore" that requires authentication to set. This prevents ad-hoc test skipping and ensures ignored tests are acknowledged by authorized users.

## Goals

1. New test state: `qualified_ignore` (only settable via authenticated command)
2. Signed database: Prevent unauthorized modifications to test_db.sdn
3. Authentication: Support OAuth (Google/MS) and password-based
4. Commands: `qualify-ignore` for batch and interactive qualification

---

## Authentication Options

### Option A: OAuth Device Flow (Recommended)

**How it works:**
1. CLI displays a URL and code: `Visit https://microsoft.com/devicelogin and enter code: ABCD1234`
2. User visits URL on any browser, enters code, authenticates
3. CLI receives token, extracts email/user ID
4. Email stored as signer in database

**Pros:**
- No password storage needed
- Uses existing corporate/personal accounts
- Strong security (2FA, etc.)
- Audit trail via email

**Cons:**
- Requires internet connection
- Needs app registration with Google/Microsoft
- More complex implementation

**Libraries:**
- Rust: `oauth2` crate with device flow support
- Google: [Device Flow for Limited Input](https://developers.google.com/identity/protocols/oauth2/limited-input-device)
- Microsoft: [Device Authorization Grant](https://learn.microsoft.com/en-us/entra/identity-platform/v2-oauth2-device-code)

### Option B: Password with Argon2

**How it works:**
1. First use: `simple qualify-ignore --set-password` (prompts for password)
2. Password hashed with Argon2id, salt stored
3. Subsequent uses: `simple qualify-ignore` (prompts for password, verifies hash)

**Pros:**
- Works offline
- Simple implementation
- No external dependencies

**Cons:**
- Password management burden
- Less secure if weak password chosen
- No identity verification

### Option C: Hybrid (Recommended for v1)

Support both methods:
- Primary: Password (simpler, works offline)
- Secondary: OAuth (for teams, audit trail)

```
simple qualify-ignore --provider password   # Uses password
simple qualify-ignore --provider google     # Uses Google OAuth
simple qualify-ignore --provider microsoft  # Uses Microsoft OAuth
```

---

## Database Signature System

### Signed SDN Format

Add signature header to protected SDN files:

```sdn
# SIGNED: Do not modify manually. Use `simple qualify-ignore` command.
# signature: sha256:<hash>
# signer: user@example.com
# signed_at: 2026-01-24T10:00:00Z

tests |test_id, ..., status, qualified_by, qualified_at|
    test/foo_spec.spl, ..., qualified_ignore, user@example.com, 2026-01-24T10:00:00Z
```

### Signature Verification

```rust
// In db_lock.rs or new signature.rs
pub struct SignedDb {
    pub hash: String,           // SHA256 of content (excluding signature header)
    pub signer: String,         // Email or "password:<hash-prefix>"
    pub signed_at: DateTime,    // Timestamp
}

fn verify_signature(path: &Path) -> Result<SignedDb, SignatureError> {
    let content = fs::read_to_string(path)?;
    let (header, body) = parse_signature_header(&content)?;

    let computed_hash = sha256(body);
    if computed_hash != header.hash {
        return Err(SignatureError::HashMismatch);
    }

    Ok(header)
}

fn sign_and_save(path: &Path, content: &str, signer: &str) -> Result<(), Error> {
    let hash = sha256(content);
    let header = format!(
        "# SIGNED: Do not modify manually. Use `simple qualify-ignore` command.\n\
         # signature: sha256:{}\n\
         # signer: {}\n\
         # signed_at: {}\n\n",
        hash, signer, Utc::now()
    );

    fs::write(path, format!("{}{}", header, content))?;
    Ok(())
}
```

### Protection Scope

| File | Signed | Reason |
|------|--------|--------|
| test_db.sdn | Yes | Contains qualified_ignore states |
| feature_db.sdn | No | Features can be updated freely |
| todo_db.sdn | No | TODOs are informational |
| task_db.sdn | No | Tasks are workflow items |

---

## New Test Status

### TestStatus Enum Update

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TestStatus {
    Passed,
    Failed,
    Skipped,
    Ignored,           // Can be set by anyone (test annotation)
    QualifiedIgnore,   // Requires authentication to set
}
```

### TestRecord Fields

```rust
pub struct TestRecord {
    // ... existing fields ...

    pub status: TestStatus,

    // New fields for qualified ignore
    pub qualified_by: Option<String>,    // Email or identifier
    pub qualified_at: Option<String>,    // ISO timestamp
    pub qualified_reason: Option<String>, // Why it's being ignored
}
```

---

## Commands

### 1. Set Password (First Time Setup)

```bash
simple qualify-ignore --set-password

# Interactive:
# Enter new password: ********
# Confirm password: ********
# Password set successfully. Hash stored in ~/.simple/auth.sdn
```

### 2. Qualify All Ignored Tests

```bash
simple qualify-ignore --all

# Interactive:
# Found 5 tests with 'ignored' status:
#   1. test/foo_spec.spl - "Missing feature X"
#   2. test/bar_spec.spl - "Flaky on CI"
#   ...
#
# Authenticate to qualify all:
# [1] Password
# [2] Google OAuth
# [3] Microsoft OAuth
# Choice: 1
# Enter password: ********
#
# Reason for qualifying (optional): Known issues, tracked in #123
#
# ✓ Qualified 5 tests as 'qualified_ignore'
# ✓ Database signed by: password:a1b2c3
```

### 3. Qualify Specific Tests

```bash
simple qualify-ignore

# Interactive:
# Tests with 'ignored' status:
#   1. test/foo_spec.spl - "Missing feature X"
#   2. test/bar_spec.spl - "Flaky on CI"
#   3. test/baz_spec.spl - "Needs refactor"
#
# Select tests to qualify (comma-separated, or 'all'): 1,3
#
# Authenticate:
# Enter password: ********
#
# Reason for qualifying: Tracked in issue #456
#
# ✓ Qualified 2 tests as 'qualified_ignore'
```

### 4. OAuth Flow Example

```bash
simple qualify-ignore --provider google

# Output:
# Visit: https://accounts.google.com/o/oauth2/device/code
# Enter code: ABCD-1234
#
# Waiting for authentication...
# ✓ Authenticated as: user@gmail.com
#
# Found 3 ignored tests. Qualify all? [Y/n]: y
# ✓ Qualified 3 tests, signed by: user@gmail.com
```

### 5. List Qualified Tests

```bash
simple test --list-qualified

# Qualified Ignored Tests:
# ┌──────────────────────────┬──────────────────┬─────────────────────┐
# │ Test                     │ Qualified By     │ Reason              │
# ├──────────────────────────┼──────────────────┼─────────────────────┤
# │ test/foo_spec.spl        │ user@gmail.com   │ Tracked in #123     │
# │ test/bar_spec.spl        │ password:a1b2c3  │ Known flaky         │
# └──────────────────────────┴──────────────────┴─────────────────────┘
```

---

## Data Flow

```
                                    ┌─────────────────┐
                                    │   User Input    │
                                    │  (password/     │
                                    │   OAuth)        │
                                    └────────┬────────┘
                                             │
                                             ▼
┌─────────────────┐    ┌─────────────────────────────────────┐
│  test_db.sdn    │◄───│         qualify-ignore CLI          │
│  (SIGNED)       │    │                                     │
└─────────────────┘    │  1. Verify current signature        │
         │             │  2. Authenticate user               │
         │             │  3. Update test statuses            │
         │             │  4. Re-sign database                │
         ▼             └─────────────────────────────────────┘
┌─────────────────┐
│  Auth Storage   │
│  ~/.simple/     │
│   auth.sdn      │    Contains: password hash, OAuth tokens
└─────────────────┘
```

---

## File Structure

```
~/.simple/
├── auth.sdn              # Authentication config (password hash, tokens)
└── oauth_cache.sdn       # Cached OAuth tokens (optional)

doc/test/
├── test_db.sdn           # SIGNED - test results with qualified_ignore
└── test_db.sdn.prev      # Backup before changes
```

### auth.sdn Format

```sdn
auth:
    password_hash: "$argon2id$v=19$m=65536,t=3,p=4$..."
    password_set_at: 2026-01-24T10:00:00Z

    oauth_providers:
        google:
            client_id: "xxx.apps.googleusercontent.com"
            refresh_token: "encrypted:..."
            email: user@gmail.com
            expires_at: 2026-02-24T10:00:00Z
```

---

## Implementation Phases

### Phase 1: Password-Based (MVP)
1. Add `QualifiedIgnore` status to `TestStatus` enum
2. Add `qualified_by`, `qualified_at`, `qualified_reason` fields to `TestRecord`
3. Implement password storage with Argon2id
4. Implement `simple qualify-ignore` command (password only)
5. Add database signature verification

### Phase 2: OAuth Support
1. Register app with Google Cloud Console
2. Register app with Microsoft Entra
3. Implement device code flow
4. Add `--provider google/microsoft` options

### Phase 3: Team Features
1. Allow multiple authorized signers
2. Signature chain (who qualified, who reviewed)
3. Integration with CI/CD (service account signing)

---

## Security Considerations

1. **Password Storage**: Use Argon2id with secure parameters
2. **OAuth Tokens**: Store encrypted, short expiry
3. **Signature Verification**: Always verify before modifying signed files
4. **Audit Trail**: Log all qualification events

### Argon2id Parameters

```rust
use argon2::{Argon2, PasswordHasher, PasswordVerifier};
use argon2::password_hash::SaltString;

// Recommended parameters (OWASP 2024)
let argon2 = Argon2::new(
    argon2::Algorithm::Argon2id,
    argon2::Version::V0x13,
    argon2::Params::new(65536, 3, 4, None).unwrap(), // 64MB, 3 iterations, 4 parallelism
);
```

---

## Questions for User

1. **OAuth Priority**: Should we implement Google, Microsoft, or both?
2. **Offline Mode**: Is password-only acceptable for v1?
3. **Team Use**: Do you need multiple authorized signers?
4. **CI/CD**: Should service accounts be able to sign?

---

## Dependencies

```toml
# Cargo.toml additions
argon2 = "0.5"           # Password hashing
sha2 = "0.10"            # Database signature
oauth2 = "4.4"           # OAuth device flow
rpassword = "7.3"        # Secure password input
```

---

## References

- [OAuth Device Flow (Microsoft)](https://learn.microsoft.com/en-us/entra/identity-platform/v2-oauth2-device-code)
- [Device Flow (Google)](https://developers.google.com/identity/protocols/oauth2/limited-input-device)
- [Argon2 OWASP Guidelines](https://cheatsheetseries.owasp.org/cheatsheets/Password_Storage_Cheat_Sheet.html)

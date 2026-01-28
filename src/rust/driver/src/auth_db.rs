//! Authentication database for qualified ignore feature.
//!
//! Stores:
//! - Password hash (Argon2id) for local authentication
//! - List of authorized email addresses for OAuth
//! - Cached OAuth tokens
//!
//! Storage location: ~/.simple/auth.sdn

use argon2::{
    password_hash::{rand_core::OsRng, PasswordHash, PasswordHasher, PasswordVerifier, SaltString},
    Argon2,
};
use serde::{Deserialize, Serialize};
use simple_sdn::{parse_document, SdnValue};
use std::collections::HashMap;
use std::fs;
use std::path::PathBuf;

/// Authentication configuration
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct AuthConfig {
    /// Argon2id password hash (if password auth is set up)
    pub password_hash: Option<String>,
    /// List of authorized email addresses for OAuth
    pub authorized_emails: Vec<String>,
    /// Cached OAuth tokens (keyed by email)
    #[serde(skip_serializing_if = "HashMap::is_empty", default)]
    pub oauth_tokens: HashMap<String, OAuthToken>,
}

/// Cached OAuth token
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OAuthToken {
    pub access_token: String,
    pub refresh_token: Option<String>,
    pub expires_at: Option<String>,
    pub provider: OAuthProvider,
}

/// OAuth provider
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum OAuthProvider {
    Google,
    Microsoft,
}

impl std::fmt::Display for OAuthProvider {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OAuthProvider::Google => write!(f, "google"),
            OAuthProvider::Microsoft => write!(f, "microsoft"),
        }
    }
}

/// Get the path to the auth config file
pub fn auth_config_path() -> PathBuf {
    dirs_next::home_dir()
        .unwrap_or_else(|| PathBuf::from("."))
        .join(".simple")
        .join("auth.sdn")
}

/// Load auth config from file
pub fn load_auth_config() -> Result<AuthConfig, String> {
    let path = auth_config_path();

    if !path.exists() {
        return Ok(AuthConfig::default());
    }

    let content = fs::read_to_string(&path).map_err(|e| format!("Failed to read auth config: {}", e))?;

    if content.trim().is_empty() {
        return Ok(AuthConfig::default());
    }

    // Try SDN format first
    match parse_document(&content) {
        Ok(doc) => parse_auth_config_sdn(&doc),
        Err(sdn_err) => {
            // Fallback to JSON
            serde_json::from_str(&content)
                .map_err(|json_err| format!("Failed to parse auth config - SDN: {}, JSON: {}", sdn_err, json_err))
        }
    }
}

/// Parse auth config from SDN document
fn parse_auth_config_sdn(doc: &simple_sdn::SdnDocument) -> Result<AuthConfig, String> {
    let root = doc.root();
    let mut config = AuthConfig::default();

    if let SdnValue::Dict(dict) = root {
        // Parse password_hash
        if let Some(SdnValue::String(hash)) = dict.get("password_hash") {
            if !hash.is_empty() {
                config.password_hash = Some(hash.clone());
            }
        }

        // Parse authorized_emails
        if let Some(SdnValue::Array(emails)) = dict.get("authorized_emails") {
            config.authorized_emails = emails
                .iter()
                .filter_map(|v| {
                    if let SdnValue::String(s) = v {
                        Some(s.clone())
                    } else {
                        None
                    }
                })
                .collect();
        }

        // Parse oauth_tokens (stored as JSON string for simplicity)
        if let Some(SdnValue::String(tokens_json)) = dict.get("oauth_tokens") {
            if let Ok(tokens) = serde_json::from_str(tokens_json) {
                config.oauth_tokens = tokens;
            }
        }
    }

    Ok(config)
}

/// Save auth config to file
pub fn save_auth_config(config: &AuthConfig) -> Result<(), String> {
    let path = auth_config_path();

    // Ensure directory exists
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| format!("Failed to create auth config directory: {}", e))?;
    }

    // Build SDN content
    let mut content = String::new();
    content.push_str("# Simple Language Auth Config\n");
    content.push_str("# DO NOT SHARE - contains authentication secrets\n\n");

    if let Some(ref hash) = config.password_hash {
        content.push_str(&format!("password_hash: \"{}\"\n", hash));
    }

    if !config.authorized_emails.is_empty() {
        content.push_str("authorized_emails: [\n");
        for email in &config.authorized_emails {
            content.push_str(&format!("    \"{}\"\n", email));
        }
        content.push_str("]\n");
    }

    if !config.oauth_tokens.is_empty() {
        let tokens_json = serde_json::to_string(&config.oauth_tokens)
            .map_err(|e| format!("Failed to serialize OAuth tokens: {}", e))?;
        content.push_str(&format!("oauth_tokens: \"{}\"\n", tokens_json.replace('"', "\\\"")));
    }

    // Atomic write
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content).map_err(|e| format!("Failed to write auth config: {}", e))?;
    fs::rename(&temp_path, &path).map_err(|e| format!("Failed to finalize auth config: {}", e))?;

    // Set restrictive permissions on Unix
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut perms = fs::metadata(&path)
            .map_err(|e| format!("Failed to get file metadata: {}", e))?
            .permissions();
        perms.set_mode(0o600); // Owner read/write only
        fs::set_permissions(&path, perms).map_err(|e| format!("Failed to set file permissions: {}", e))?;
    }

    Ok(())
}

/// Hash a password using Argon2id
pub fn hash_password(password: &str) -> Result<String, String> {
    let salt = SaltString::generate(&mut OsRng);
    let argon2 = Argon2::default();

    argon2
        .hash_password(password.as_bytes(), &salt)
        .map(|hash| hash.to_string())
        .map_err(|e| format!("Failed to hash password: {}", e))
}

/// Verify a password against a stored hash
pub fn verify_password(password: &str, hash: &str) -> Result<bool, String> {
    let parsed_hash = PasswordHash::new(hash).map_err(|e| format!("Invalid password hash format: {}", e))?;

    Ok(Argon2::default()
        .verify_password(password.as_bytes(), &parsed_hash)
        .is_ok())
}

/// Check if password authentication is set up
pub fn is_password_set() -> Result<bool, String> {
    let config = load_auth_config()?;
    Ok(config.password_hash.is_some())
}

/// Add an authorized email
pub fn add_authorized_email(email: &str) -> Result<(), String> {
    let mut config = load_auth_config()?;

    // Normalize email to lowercase
    let email = email.to_lowercase();

    if config.authorized_emails.contains(&email) {
        return Err(format!("Email '{}' is already authorized", email));
    }

    config.authorized_emails.push(email);
    save_auth_config(&config)
}

/// Remove an authorized email
pub fn remove_authorized_email(email: &str) -> Result<(), String> {
    let mut config = load_auth_config()?;

    let email = email.to_lowercase();
    let original_len = config.authorized_emails.len();
    config.authorized_emails.retain(|e| e != &email);

    if config.authorized_emails.len() == original_len {
        return Err(format!("Email '{}' was not in authorized list", email));
    }

    save_auth_config(&config)
}

/// Check if an email is authorized
pub fn is_email_authorized(email: &str) -> Result<bool, String> {
    let config = load_auth_config()?;
    let email = email.to_lowercase();
    Ok(config.authorized_emails.iter().any(|e| e == &email))
}

/// Set the password (first time or update)
pub fn set_password(password: &str) -> Result<(), String> {
    if password.len() < 8 {
        return Err("Password must be at least 8 characters".to_string());
    }

    let hash = hash_password(password)?;
    let mut config = load_auth_config()?;
    config.password_hash = Some(hash);
    save_auth_config(&config)
}

/// Authenticate with password
pub fn authenticate_password(password: &str) -> Result<String, String> {
    let config = load_auth_config()?;

    match config.password_hash {
        Some(ref hash) => {
            if verify_password(password, hash)? {
                // Return a signer identifier (first 8 chars of hash)
                let hash_prefix = &hash[hash.len().saturating_sub(12)..];
                Ok(format!("password:{}", hash_prefix))
            } else {
                Err("Invalid password".to_string())
            }
        }
        None => Err("Password authentication not set up. Use --set-password first.".to_string()),
    }
}

/// Store OAuth token
pub fn store_oauth_token(email: &str, token: OAuthToken) -> Result<(), String> {
    let mut config = load_auth_config()?;
    config.oauth_tokens.insert(email.to_lowercase(), token);
    save_auth_config(&config)
}

/// Get cached OAuth token
pub fn get_oauth_token(email: &str) -> Result<Option<OAuthToken>, String> {
    let config = load_auth_config()?;
    Ok(config.oauth_tokens.get(&email.to_lowercase()).cloned())
}

/// Clear all OAuth tokens
pub fn clear_oauth_tokens() -> Result<(), String> {
    let mut config = load_auth_config()?;
    config.oauth_tokens.clear();
    save_auth_config(&config)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_password_hash_verify() {
        let password = "test_password_123";
        let hash = hash_password(password).unwrap();

        assert!(verify_password(password, &hash).unwrap());
        assert!(!verify_password("wrong_password", &hash).unwrap());
    }

    #[test]
    fn test_auth_config_default() {
        let config = AuthConfig::default();
        assert!(config.password_hash.is_none());
        assert!(config.authorized_emails.is_empty());
        assert!(config.oauth_tokens.is_empty());
    }
}

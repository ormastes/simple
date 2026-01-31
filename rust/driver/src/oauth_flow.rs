//! OAuth Device Code Flow implementation for qualified ignore authentication.
//!
//! Supports:
//! - Google OAuth (device code flow)
//! - Microsoft OAuth / Entra ID (device code flow)
//!
//! Device code flow is ideal for CLI applications as it doesn't require
//! a redirect URI or browser automation.

use crate::auth_db::{is_email_authorized, store_oauth_token, OAuthProvider, OAuthToken};
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};

/// OAuth configuration for providers
#[derive(Debug, Clone)]
pub struct OAuthConfig {
    pub provider: OAuthProvider,
    pub client_id: String,
    pub device_auth_endpoint: String,
    pub token_endpoint: String,
    pub scopes: Vec<String>,
}

impl OAuthConfig {
    /// Get Google OAuth configuration
    ///
    /// Requires a client ID from Google Cloud Console.
    /// Create at: https://console.cloud.google.com/apis/credentials
    pub fn google(client_id: &str) -> Self {
        Self {
            provider: OAuthProvider::Google,
            client_id: client_id.to_string(),
            device_auth_endpoint: "https://oauth2.googleapis.com/device/code".to_string(),
            token_endpoint: "https://oauth2.googleapis.com/token".to_string(),
            scopes: vec!["openid".to_string(), "email".to_string(), "profile".to_string()],
        }
    }

    /// Get Microsoft OAuth configuration
    ///
    /// Requires a client ID from Azure AD / Entra.
    /// Create at: https://portal.azure.com/#blade/Microsoft_AAD_RegisteredApps
    pub fn microsoft(client_id: &str) -> Self {
        Self {
            provider: OAuthProvider::Microsoft,
            client_id: client_id.to_string(),
            device_auth_endpoint: "https://login.microsoftonline.com/common/oauth2/v2.0/devicecode".to_string(),
            token_endpoint: "https://login.microsoftonline.com/common/oauth2/v2.0/token".to_string(),
            scopes: vec![
                "openid".to_string(),
                "email".to_string(),
                "profile".to_string(),
                "offline_access".to_string(),
            ],
        }
    }
}

/// Device code response from OAuth provider
#[derive(Debug, Deserialize)]
pub struct DeviceCodeResponse {
    pub device_code: String,
    pub user_code: String,
    pub verification_uri: String,
    #[serde(default)]
    pub verification_uri_complete: Option<String>,
    pub expires_in: u64,
    pub interval: Option<u64>,
}

/// Token response from OAuth provider
#[derive(Debug, Deserialize)]
pub struct TokenResponse {
    pub access_token: String,
    pub token_type: String,
    pub expires_in: Option<u64>,
    pub refresh_token: Option<String>,
    pub scope: Option<String>,
    pub id_token: Option<String>,
}

/// Token error response
#[derive(Debug, Deserialize)]
pub struct TokenErrorResponse {
    pub error: String,
    pub error_description: Option<String>,
}

/// User info from ID token or userinfo endpoint
#[derive(Debug, Deserialize)]
pub struct UserInfo {
    pub email: Option<String>,
    pub name: Option<String>,
    pub sub: String,
}

/// Result of device code flow
#[derive(Debug)]
pub struct DeviceFlowResult {
    pub email: String,
    pub access_token: String,
    pub refresh_token: Option<String>,
    pub provider: OAuthProvider,
}

/// Load OAuth client configuration from environment or config file
pub fn load_oauth_config(provider: OAuthProvider) -> Result<OAuthConfig, String> {
    match provider {
        OAuthProvider::Google => {
            let client_id = std::env::var("SIMPLE_GOOGLE_CLIENT_ID")
                .or_else(|_| load_client_id_from_config("google"))
                .map_err(|_| {
                    "Google OAuth not configured. Set SIMPLE_GOOGLE_CLIENT_ID environment variable \
                     or add google_client_id to ~/.simple/oauth.sdn"
                })?;
            Ok(OAuthConfig::google(&client_id))
        }
        OAuthProvider::Microsoft => {
            let client_id = std::env::var("SIMPLE_MICROSOFT_CLIENT_ID")
                .or_else(|_| load_client_id_from_config("microsoft"))
                .map_err(|_| {
                    "Microsoft OAuth not configured. Set SIMPLE_MICROSOFT_CLIENT_ID environment variable \
                     or add microsoft_client_id to ~/.simple/oauth.sdn"
                })?;
            Ok(OAuthConfig::microsoft(&client_id))
        }
    }
}

/// Load client ID from config file
fn load_client_id_from_config(provider: &str) -> Result<String, String> {
    let config_path = dirs_next::home_dir()
        .ok_or("Cannot find home directory")?
        .join(".simple")
        .join("oauth.sdn");

    if !config_path.exists() {
        return Err("Config file not found".to_string());
    }

    let content = std::fs::read_to_string(&config_path).map_err(|e| format!("Failed to read config: {}", e))?;

    // Simple parsing - look for provider_client_id: "value"
    let key = format!("{}_client_id", provider);
    for line in content.lines() {
        let line = line.trim();
        if line.starts_with(&key) {
            if let Some(value) = line.split(':').nth(1) {
                let value = value.trim().trim_matches('"').trim_matches('\'');
                if !value.is_empty() {
                    return Ok(value.to_string());
                }
            }
        }
    }

    Err(format!("Client ID for {} not found in config", provider))
}

/// Execute the device code flow (blocking)
///
/// This function:
/// 1. Requests a device code from the OAuth provider
/// 2. Displays instructions to the user
/// 3. Polls for the access token
/// 4. Retrieves user info to get email
/// 5. Verifies the email is authorized
/// 6. Stores the token for future use
pub fn device_code_flow(provider: OAuthProvider) -> Result<DeviceFlowResult, String> {
    let config = load_oauth_config(provider)?;
    let agent = ureq::Agent::new();

    // Step 1: Request device code
    println!("Requesting device code from {}...", config.provider);

    let device_code_response = request_device_code(&agent, &config)?;

    // Step 2: Display instructions
    println!();
    println!("=== Authentication Required ===");
    println!();
    println!("To authenticate, visit:");
    if let Some(ref complete_uri) = device_code_response.verification_uri_complete {
        println!("  {}", complete_uri);
    } else {
        println!("  {}", device_code_response.verification_uri);
        println!();
        println!("And enter code: {}", device_code_response.user_code);
    }
    println!();
    println!(
        "Waiting for authentication (expires in {} seconds)...",
        device_code_response.expires_in
    );

    // Step 3: Poll for token
    let poll_interval = Duration::from_secs(device_code_response.interval.unwrap_or(5));
    let deadline = Instant::now() + Duration::from_secs(device_code_response.expires_in);

    let token_response = poll_for_token(
        &agent,
        &config,
        &device_code_response.device_code,
        poll_interval,
        deadline,
    )?;

    println!("Authentication successful!");

    // Step 4: Get user info
    let user_info = get_user_info(&agent, &token_response.access_token, &config)?;

    let email = user_info.email.ok_or("OAuth response did not include email")?;
    println!("Authenticated as: {}", email);

    // Step 5: Verify email is authorized
    if !is_email_authorized(&email)? {
        return Err(format!(
            "Email '{}' is not authorized. Add it with: simple qualify-ignore --add-signer {}",
            email, email
        ));
    }

    // Step 6: Store token
    let oauth_token = OAuthToken {
        access_token: token_response.access_token.clone(),
        refresh_token: token_response.refresh_token.clone(),
        expires_at: token_response
            .expires_in
            .map(|secs| (chrono::Utc::now() + chrono::Duration::seconds(secs as i64)).to_rfc3339()),
        provider,
    };
    store_oauth_token(&email, oauth_token)?;

    Ok(DeviceFlowResult {
        email,
        access_token: token_response.access_token,
        refresh_token: token_response.refresh_token,
        provider,
    })
}

/// Request a device code from the OAuth provider
fn request_device_code(agent: &ureq::Agent, config: &OAuthConfig) -> Result<DeviceCodeResponse, String> {
    let scope = config.scopes.join(" ");

    let params = [("client_id", config.client_id.as_str()), ("scope", &scope)];

    let response = agent
        .post(&config.device_auth_endpoint)
        .send_form(&params)
        .map_err(|e| format!("Failed to request device code: {}", e))?;

    if response.status() != 200 {
        let status = response.status();
        let body = response.into_string().unwrap_or_default();
        return Err(format!("Device code request failed ({}): {}", status, body));
    }

    response
        .into_json::<DeviceCodeResponse>()
        .map_err(|e| format!("Failed to parse device code response: {}", e))
}

/// Poll for the access token
fn poll_for_token(
    agent: &ureq::Agent,
    config: &OAuthConfig,
    device_code: &str,
    interval: Duration,
    deadline: Instant,
) -> Result<TokenResponse, String> {
    let grant_type = match config.provider {
        OAuthProvider::Google => "urn:ietf:params:oauth:grant-type:device_code",
        OAuthProvider::Microsoft => "urn:ietf:params:oauth:grant-type:device_code",
    };

    loop {
        if Instant::now() > deadline {
            return Err("Authentication timed out".to_string());
        }

        std::thread::sleep(interval);

        let params = [
            ("client_id", config.client_id.as_str()),
            ("device_code", device_code),
            ("grant_type", grant_type),
        ];

        let response = agent
            .post(&config.token_endpoint)
            .send_form(&params)
            .map_err(|e| format!("Failed to poll for token: {}", e))?;

        if response.status() == 200 {
            return response
                .into_json::<TokenResponse>()
                .map_err(|e| format!("Failed to parse token response: {}", e));
        }

        // Check for pending/slow_down errors
        let error_response: TokenErrorResponse = response
            .into_json()
            .map_err(|e| format!("Failed to parse error response: {}", e))?;

        match error_response.error.as_str() {
            "authorization_pending" => {
                // User hasn't completed auth yet, continue polling
                print!(".");
                std::io::Write::flush(&mut std::io::stdout()).ok();
            }
            "slow_down" => {
                // Need to slow down polling
                std::thread::sleep(interval);
            }
            "expired_token" => {
                return Err("Device code expired. Please try again.".to_string());
            }
            "access_denied" => {
                return Err("Access denied by user.".to_string());
            }
            _ => {
                return Err(format!(
                    "Token error: {} - {}",
                    error_response.error,
                    error_response.error_description.unwrap_or_default()
                ));
            }
        }
    }
}

/// Get user info from userinfo endpoint or ID token
fn get_user_info(
    agent: &ureq::Agent,
    access_token: &str,
    config: &OAuthConfig,
) -> Result<UserInfo, String> {
    let userinfo_endpoint = match config.provider {
        OAuthProvider::Google => "https://openidconnect.googleapis.com/v1/userinfo",
        OAuthProvider::Microsoft => "https://graph.microsoft.com/oidc/userinfo",
    };

    let response = agent
        .get(userinfo_endpoint)
        .set("Authorization", &format!("Bearer {}", access_token))
        .call()
        .map_err(|e| format!("Failed to get user info: {}", e))?;

    if response.status() != 200 {
        let status = response.status();
        let body = response.into_string().unwrap_or_default();
        return Err(format!("User info request failed ({}): {}", status, body));
    }

    response
        .into_json::<UserInfo>()
        .map_err(|e| format!("Failed to parse user info: {}", e))
}

/// Refresh an expired access token
pub fn refresh_access_token(provider: OAuthProvider, refresh_token: &str) -> Result<TokenResponse, String> {
    let config = load_oauth_config(provider)?;
    let agent = ureq::Agent::new();

    let params = [
        ("client_id", config.client_id.as_str()),
        ("refresh_token", refresh_token),
        ("grant_type", "refresh_token"),
    ];

    let response = agent
        .post(&config.token_endpoint)
        .send_form(&params)
        .map_err(|e| format!("Failed to refresh token: {}", e))?;

    if response.status() != 200 {
        let status = response.status();
        let body = response.into_string().unwrap_or_default();
        return Err(format!("Token refresh failed ({}): {}", status, body));
    }

    response
        .into_json::<TokenResponse>()
        .map_err(|e| format!("Failed to parse refresh response: {}", e))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_google_config() {
        let config = OAuthConfig::google("test-client-id");
        assert_eq!(config.provider, OAuthProvider::Google);
        assert_eq!(config.client_id, "test-client-id");
        assert!(config.scopes.contains(&"email".to_string()));
    }

    #[test]
    fn test_microsoft_config() {
        let config = OAuthConfig::microsoft("test-client-id");
        assert_eq!(config.provider, OAuthProvider::Microsoft);
        assert_eq!(config.client_id, "test-client-id");
        assert!(config.scopes.contains(&"offline_access".to_string()));
    }
}

//! CLI commands for qualified ignore management.
//!
//! Commands:
//! - `simple qualify-ignore --set-password` - Set up password authentication
//! - `simple qualify-ignore --add-signer <email>` - Add authorized OAuth email
//! - `simple qualify-ignore --remove-signer <email>` - Remove authorized email
//! - `simple qualify-ignore --list-signers` - List authorized signers
//! - `simple qualify-ignore --all` - Qualify all currently ignored tests
//! - `simple qualify-ignore <test-id>` - Qualify specific test(s)
//! - `simple qualify-ignore --unqualify <test-id>` - Remove qualification
//! - `simple qualify-ignore --verify` - Verify signature integrity
//! - `simple qualify-ignore --status` - Show qualification status

use crate::auth_db::{
    add_authorized_email, authenticate_password, is_password_set, load_auth_config, remove_authorized_email,
    set_password, OAuthProvider,
};
#[cfg(feature = "oauth")]
use crate::oauth_flow::device_code_flow;
use crate::signature::{
    has_qualified_ignores, load_signature_from_db, save_signature_to_db, sign_qualified_ignores, verify_signature,
    get_qualified_ignore_ids,
};
use crate::test_db::{load_test_db, save_test_db, TestDb, TestStatus};
use std::path::PathBuf;

/// Qualified ignore command arguments
pub struct QualifyIgnoreArgs {
    /// Set up password authentication
    pub set_password: bool,
    /// Add an authorized signer email
    pub add_signer: Option<String>,
    /// Remove an authorized signer
    pub remove_signer: Option<String>,
    /// List all authorized signers
    pub list_signers: bool,
    /// Qualify all currently ignored tests
    pub all: bool,
    /// Authentication provider to use
    pub provider: AuthProvider,
    /// Specific test IDs to qualify
    pub test_ids: Vec<String>,
    /// Unqualify specific tests (requires re-authentication)
    pub unqualify: Vec<String>,
    /// Verify signature integrity
    pub verify: bool,
    /// Show qualification status
    pub status: bool,
    /// Reason for qualification
    pub reason: Option<String>,
    /// Path to test database
    pub db_path: Option<PathBuf>,
}

/// Authentication provider
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum AuthProvider {
    #[default]
    Password,
    #[cfg(feature = "oauth")]
    Google,
    #[cfg(feature = "oauth")]
    Microsoft,
}

impl Default for QualifyIgnoreArgs {
    fn default() -> Self {
        Self {
            set_password: false,
            add_signer: None,
            remove_signer: None,
            list_signers: false,
            all: false,
            provider: AuthProvider::Password,
            test_ids: Vec::new(),
            unqualify: Vec::new(),
            verify: false,
            status: false,
            reason: None,
            db_path: None,
        }
    }
}

/// Parse qualify-ignore arguments from command line
pub fn parse_qualify_ignore_args(args: &[String]) -> QualifyIgnoreArgs {
    let mut result = QualifyIgnoreArgs::default();
    let mut i = 0;

    while i < args.len() {
        let arg = &args[i];

        match arg.as_str() {
            "--set-password" => result.set_password = true,
            "--add-signer" => {
                if i + 1 < args.len() {
                    i += 1;
                    result.add_signer = Some(args[i].clone());
                }
            }
            "--remove-signer" => {
                if i + 1 < args.len() {
                    i += 1;
                    result.remove_signer = Some(args[i].clone());
                }
            }
            "--list-signers" => result.list_signers = true,
            "--all" | "-a" => result.all = true,
            "--provider" | "-p" => {
                if i + 1 < args.len() {
                    i += 1;
                    result.provider = match args[i].to_lowercase().as_str() {
                        #[cfg(feature = "oauth")]
                        "google" => AuthProvider::Google,
                        #[cfg(feature = "oauth")]
                        "microsoft" => AuthProvider::Microsoft,
                        #[cfg(not(feature = "oauth"))]
                        "google" | "microsoft" => {
                            eprintln!("Error: OAuth providers require the 'oauth' feature. Rebuild with --features oauth");
                            AuthProvider::Password
                        }
                        _ => AuthProvider::Password,
                    };
                }
            }
            "--unqualify" => {
                if i + 1 < args.len() {
                    i += 1;
                    result.unqualify.push(args[i].clone());
                }
            }
            "--verify" => result.verify = true,
            "--status" => result.status = true,
            "--reason" | "-r" => {
                if i + 1 < args.len() {
                    i += 1;
                    result.reason = Some(args[i].clone());
                }
            }
            "--db" => {
                if i + 1 < args.len() {
                    i += 1;
                    result.db_path = Some(PathBuf::from(&args[i]));
                }
            }
            _ if !arg.starts_with('-') => {
                result.test_ids.push(arg.clone());
            }
            _ => {}
        }

        i += 1;
    }

    result
}

/// Execute the qualify-ignore command
pub fn handle_qualify_ignore(args: QualifyIgnoreArgs) -> Result<(), String> {
    // Determine database path
    let db_path = args.db_path.clone().unwrap_or_else(|| {
        let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        cwd.join("doc/test/test_db.sdn")
    });

    // Handle configuration commands first (no auth required)
    if args.set_password {
        return handle_set_password();
    }

    if let Some(ref email) = args.add_signer {
        return handle_add_signer(email);
    }

    if let Some(ref email) = args.remove_signer {
        return handle_remove_signer(email);
    }

    if args.list_signers {
        return handle_list_signers();
    }

    if args.status {
        return handle_status(&db_path);
    }

    if args.verify {
        return handle_verify(&db_path);
    }

    // Operations requiring authentication
    if args.all {
        return handle_qualify_all(&db_path, &args);
    }

    if !args.unqualify.is_empty() {
        return handle_unqualify(&db_path, &args.unqualify, &args);
    }

    if !args.test_ids.is_empty() {
        return handle_qualify_specific(&db_path, &args.test_ids, &args);
    }

    // No operation specified - show help
    print_help();
    Ok(())
}

fn print_help() {
    println!("Usage: simple qualify-ignore [OPTIONS] [TEST_IDS...]");
    println!();
    println!("Manage qualified ignore status for tests.");
    println!();
    println!("Setup Commands:");
    println!("  --set-password           Set up password authentication");
    println!("  --add-signer <email>     Add authorized OAuth email");
    println!("  --remove-signer <email>  Remove authorized signer");
    println!("  --list-signers           List all authorized signers");
    println!();
    println!("Qualification Commands:");
    println!("  --all, -a                Qualify all currently ignored tests");
    println!("  --unqualify <test-id>    Remove qualification (re-auth required)");
    println!("  <test-id>...             Qualify specific test(s)");
    println!();
    println!("Options:");
    #[cfg(feature = "oauth")]
    println!("  --provider, -p <type>    Auth provider: password, google, microsoft");
    #[cfg(not(feature = "oauth"))]
    println!("  --provider, -p <type>    Auth provider: password (rebuild with --features oauth for OAuth)");
    println!("  --reason, -r <text>      Reason for qualification");
    println!("  --db <path>              Path to test database");
    println!();
    println!("Status Commands:");
    println!("  --status                 Show qualification status");
    println!("  --verify                 Verify signature integrity");
    println!();
    #[cfg(feature = "oauth")]
    {
        println!("OAuth Configuration:");
        println!("  For Google: Set SIMPLE_GOOGLE_CLIENT_ID or add to ~/.simple/oauth.sdn");
        println!("  For Microsoft: Set SIMPLE_MICROSOFT_CLIENT_ID or add to ~/.simple/oauth.sdn");
        println!();
    }
    println!("Examples:");
    println!("  simple qualify-ignore --set-password      # Set up password auth");
    println!("  simple qualify-ignore --all -r \"CI flaky\" # Qualify all ignored tests");
    println!("  simple qualify-ignore --status            # Show current status");
}

fn handle_set_password() -> Result<(), String> {
    println!("Setting up password authentication for qualified ignore.");
    println!();

    if is_password_set()? {
        println!("Warning: Password is already set. This will replace it.");
        print!("Continue? [y/N] ");
        std::io::Write::flush(&mut std::io::stdout()).ok();

        let mut input = String::new();
        std::io::stdin().read_line(&mut input).ok();
        if !input.trim().eq_ignore_ascii_case("y") {
            println!("Aborted.");
            return Ok(());
        }
    }

    let password = rpassword::prompt_password("Enter new password (min 8 chars): ")
        .map_err(|e| format!("Failed to read password: {}", e))?;

    if password.len() < 8 {
        return Err("Password must be at least 8 characters".to_string());
    }

    let confirm =
        rpassword::prompt_password("Confirm password: ").map_err(|e| format!("Failed to read password: {}", e))?;

    if password != confirm {
        return Err("Passwords do not match".to_string());
    }

    set_password(&password)?;
    println!("Password set successfully.");
    Ok(())
}

fn handle_add_signer(email: &str) -> Result<(), String> {
    add_authorized_email(email)?;
    println!("Added authorized signer: {}", email);
    Ok(())
}

fn handle_remove_signer(email: &str) -> Result<(), String> {
    remove_authorized_email(email)?;
    println!("Removed authorized signer: {}", email);
    Ok(())
}

fn handle_list_signers() -> Result<(), String> {
    let config = load_auth_config()?;

    println!("Authorized Signers:");
    println!("-------------------");

    if config.password_hash.is_some() {
        println!("  [password] Password authentication enabled");
    }

    if config.authorized_emails.is_empty() {
        if config.password_hash.is_none() {
            println!("  (none configured)");
        }
    } else {
        for email in &config.authorized_emails {
            println!("  [oauth] {}", email);
        }
    }

    Ok(())
}

fn handle_status(db_path: &PathBuf) -> Result<(), String> {
    let db = load_test_db(db_path)?;

    let qualified_count = db
        .records
        .values()
        .filter(|r| r.status == TestStatus::QualifiedIgnore)
        .count();

    let ignored_count = db.records.values().filter(|r| r.status == TestStatus::Ignored).count();

    println!("Qualified Ignore Status");
    println!("=======================");
    println!("Database: {}", db_path.display());
    println!();
    println!("Tests with qualified_ignore: {}", qualified_count);
    println!("Tests with regular ignore:   {}", ignored_count);
    println!();

    if qualified_count > 0 {
        println!("Qualified Tests:");
        for (id, record) in &db.records {
            if record.status == TestStatus::QualifiedIgnore {
                let qualified_by = record.qualified_by.as_deref().unwrap_or("-");
                let reason = record.qualified_reason.as_deref().unwrap_or("-");
                println!("  {} - {} ({})", id, reason, qualified_by);
            }
        }
        println!();
    }

    // Check signature
    if let Some(sig) = load_signature_from_db(db_path)? {
        let result = verify_signature(&db, &sig);
        if result.is_valid() {
            println!("Signature: VALID");
            println!("  Signed by: {}", sig.signer);
            println!("  Signed at: {}", sig.signed_at);
        } else {
            println!("Signature: INVALID - {}", result);
        }
    } else {
        println!("Signature: Not signed");
    }

    Ok(())
}

fn handle_verify(db_path: &PathBuf) -> Result<(), String> {
    let db = load_test_db(db_path)?;

    if !has_qualified_ignores(&db) {
        println!("No qualified_ignore records to verify.");
        return Ok(());
    }

    match load_signature_from_db(db_path)? {
        Some(sig) => {
            let result = verify_signature(&db, &sig);
            if result.is_valid() {
                println!("Signature verification: PASSED");
                println!("  Signer: {}", sig.signer);
                println!("  Signed at: {}", sig.signed_at);
                println!("  Records covered: {}", sig.record_count);
            } else {
                println!("Signature verification: FAILED");
                println!("  Error: {}", result);
                return Err("Signature verification failed".to_string());
            }
        }
        None => {
            println!(
                "No signature found for {} qualified_ignore records.",
                get_qualified_ignore_ids(&db).len()
            );
            println!("Run `simple qualify-ignore --all` to sign them.");
        }
    }

    Ok(())
}

fn authenticate(args: &QualifyIgnoreArgs) -> Result<String, String> {
    match args.provider {
        AuthProvider::Password => {
            if !is_password_set()? {
                return Err("Password not set. Run `simple qualify-ignore --set-password` first.".to_string());
            }

            let password = rpassword::prompt_password("Enter password: ")
                .map_err(|e| format!("Failed to read password: {}", e))?;

            authenticate_password(&password)
        }
        #[cfg(feature = "oauth")]
        AuthProvider::Google => {
            let result = device_code_flow(OAuthProvider::Google)?;
            Ok(result.email)
        }
        #[cfg(feature = "oauth")]
        AuthProvider::Microsoft => {
            let result = device_code_flow(OAuthProvider::Microsoft)?;
            Ok(result.email)
        }
    }
}

fn handle_qualify_all(db_path: &PathBuf, args: &QualifyIgnoreArgs) -> Result<(), String> {
    let mut db = load_test_db(db_path)?;

    // Find all ignored tests
    let ignored_ids: Vec<String> = db
        .records
        .iter()
        .filter(|(_, r)| r.status == TestStatus::Ignored)
        .map(|(id, _)| id.clone())
        .collect();

    if ignored_ids.is_empty() {
        println!("No ignored tests to qualify.");
        return Ok(());
    }

    println!("Found {} ignored test(s) to qualify:", ignored_ids.len());
    for id in &ignored_ids {
        println!("  - {}", id);
    }
    println!();

    // Authenticate
    let signer = authenticate(args)?;
    println!("Authenticated as: {}", signer);

    // Get or prompt for reason
    let reason = args.reason.clone().unwrap_or_else(|| {
        print!("Reason for qualification: ");
        std::io::Write::flush(&mut std::io::stdout()).ok();
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).ok();
        input.trim().to_string()
    });

    if reason.is_empty() {
        return Err("Reason is required for qualified ignore".to_string());
    }

    // Update records
    let now = chrono::Utc::now().to_rfc3339();
    for id in &ignored_ids {
        if let Some(record) = db.records.get_mut(id) {
            record.status = TestStatus::QualifiedIgnore;
            record.qualified_by = Some(signer.clone());
            record.qualified_at = Some(now.clone());
            record.qualified_reason = Some(reason.clone());
        }
    }

    // Sign and save
    let sig = sign_qualified_ignores(&db, &signer);
    save_test_db(db_path, &db)?;
    save_signature_to_db(db_path, &sig)?;

    println!();
    println!("Qualified {} test(s).", ignored_ids.len());
    println!("Signature saved.");

    Ok(())
}

fn handle_qualify_specific(db_path: &PathBuf, test_ids: &[String], args: &QualifyIgnoreArgs) -> Result<(), String> {
    let mut db = load_test_db(db_path)?;

    // Validate test IDs exist and are ignored
    let mut to_qualify = Vec::new();
    for id in test_ids {
        match db.records.get(id) {
            Some(record) => {
                if record.status == TestStatus::Ignored {
                    to_qualify.push(id.clone());
                } else if record.status == TestStatus::QualifiedIgnore {
                    println!("Warning: {} is already qualified_ignore", id);
                } else {
                    println!("Warning: {} has status {:?}, not ignored", id, record.status);
                }
            }
            None => {
                println!("Warning: Test {} not found in database", id);
            }
        }
    }

    if to_qualify.is_empty() {
        return Err("No valid tests to qualify".to_string());
    }

    println!("Will qualify {} test(s):", to_qualify.len());
    for id in &to_qualify {
        println!("  - {}", id);
    }
    println!();

    // Authenticate
    let signer = authenticate(args)?;
    println!("Authenticated as: {}", signer);

    // Get or prompt for reason
    let reason = args.reason.clone().unwrap_or_else(|| {
        print!("Reason for qualification: ");
        std::io::Write::flush(&mut std::io::stdout()).ok();
        let mut input = String::new();
        std::io::stdin().read_line(&mut input).ok();
        input.trim().to_string()
    });

    if reason.is_empty() {
        return Err("Reason is required for qualified ignore".to_string());
    }

    // Update records
    let now = chrono::Utc::now().to_rfc3339();
    for id in &to_qualify {
        if let Some(record) = db.records.get_mut(id) {
            record.status = TestStatus::QualifiedIgnore;
            record.qualified_by = Some(signer.clone());
            record.qualified_at = Some(now.clone());
            record.qualified_reason = Some(reason.clone());
        }
    }

    // Sign and save
    let sig = sign_qualified_ignores(&db, &signer);
    save_test_db(db_path, &db)?;
    save_signature_to_db(db_path, &sig)?;

    println!();
    println!("Qualified {} test(s).", to_qualify.len());
    println!("Signature saved.");

    Ok(())
}

fn handle_unqualify(db_path: &PathBuf, test_ids: &[String], args: &QualifyIgnoreArgs) -> Result<(), String> {
    let mut db = load_test_db(db_path)?;

    // Validate test IDs exist and are qualified_ignore
    let mut to_unqualify = Vec::new();
    for id in test_ids {
        match db.records.get(id) {
            Some(record) => {
                if record.status == TestStatus::QualifiedIgnore {
                    to_unqualify.push(id.clone());
                } else {
                    println!("Warning: {} is not qualified_ignore", id);
                }
            }
            None => {
                println!("Warning: Test {} not found in database", id);
            }
        }
    }

    if to_unqualify.is_empty() {
        return Err("No valid tests to unqualify".to_string());
    }

    println!("Will unqualify {} test(s):", to_unqualify.len());
    for id in &to_unqualify {
        println!("  - {}", id);
    }
    println!();

    // Require authentication to unqualify
    let _signer = authenticate(args)?;
    println!("Authentication verified.");

    // Update records - revert to regular Ignored status
    for id in &to_unqualify {
        if let Some(record) = db.records.get_mut(id) {
            record.status = TestStatus::Ignored;
            record.qualified_by = None;
            record.qualified_at = None;
            record.qualified_reason = None;
        }
    }

    // Re-sign if there are remaining qualified_ignore records
    save_test_db(db_path, &db)?;

    if has_qualified_ignores(&db) {
        let signer = authenticate(args)?;
        let sig = sign_qualified_ignores(&db, &signer);
        save_signature_to_db(db_path, &sig)?;
        println!("Signature updated.");
    } else {
        // Remove signature file if no qualified_ignores remain
        let sig_path = db_path.with_extension("sig.sdn");
        if sig_path.exists() {
            std::fs::remove_file(&sig_path).ok();
            println!("Signature removed (no qualified_ignore records remain).");
        }
    }

    println!();
    println!("Unqualified {} test(s).", to_unqualify.len());

    Ok(())
}

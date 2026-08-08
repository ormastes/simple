pub fn seed_warning_suppressed(args: &[String]) -> bool {
    seed_warning_suppressed_with_env(
        args,
        std::env::var("SIMPLE_RUST_SEED_WARNING").ok().as_deref(),
        std::env::var("SIMPLE_BOOTSTRAP").ok().as_deref(),
    )
}

fn seed_warning_suppressed_with_env(args: &[String], rust_seed_warning: Option<&str>, bootstrap: Option<&str>) -> bool {
    if rust_seed_warning == Some("0") {
        return true;
    }
    if bootstrap == Some("1") {
        return true;
    }
    args.iter().any(|arg| arg == "--seed-ok" || arg == "--rust-seed-ok")
}

pub fn print_seed_warning() {
    eprintln!("WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.");
    eprintln!("Build and use the pure-Simple bin/simple instead.");
}

#[cfg(test)]
mod tests {
    use super::seed_warning_suppressed_with_env;

    fn args(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| value.to_string()).collect()
    }

    #[test]
    fn suppresses_seed_warning_for_bootstrap_and_ack_flags() {
        assert!(seed_warning_suppressed_with_env(&args(&["check"]), Some("0"), None));
        assert!(seed_warning_suppressed_with_env(&args(&["check"]), None, Some("1")));
        assert!(seed_warning_suppressed_with_env(
            &args(&["check", "--rust-seed-ok"]),
            None,
            None
        ));
    }

    #[test]
    fn keeps_warning_enabled_for_normal_rust_seed_tooling() {
        assert!(!seed_warning_suppressed_with_env(
            &args(&["check", "src/compiler"]),
            None,
            None
        ));
        assert!(!seed_warning_suppressed_with_env(&args(&["--help"]), None, None));
        assert!(!seed_warning_suppressed_with_env(&args(&["--version"]), None, None));
    }
}

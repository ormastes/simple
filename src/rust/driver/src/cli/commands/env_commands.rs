//! Environment management command handlers

use crate::cli::env;

/// Handle 'env' command - manage virtual environments
pub fn handle_env(args: &[String]) -> i32 {
    let subcommand = args.get(1).map(|s| s.as_str());

    match subcommand {
        Some("create") => {
            if args.len() < 3 {
                eprintln!("error: env create requires a name");
                eprintln!("Usage: simple env create <name>");
                return 1;
            }
            env::create_env(&args[2])
        }
        Some("activate") => {
            if args.len() < 3 {
                eprintln!("error: env activate requires a name");
                eprintln!("Usage: simple env activate <name>");
                return 1;
            }
            let shell = args.get(3).map(|s| s.as_str());
            env::activate_env(&args[2], shell)
        }
        Some("list") => env::list_envs(),
        Some("remove") => {
            if args.len() < 3 {
                eprintln!("error: env remove requires a name");
                eprintln!("Usage: simple env remove <name> [--force]");
                return 1;
            }
            let force = args.iter().any(|a| a == "--force");
            env::remove_env(&args[2], force)
        }
        Some("info") => {
            if args.len() < 3 {
                eprintln!("error: env info requires a name");
                eprintln!("Usage: simple env info <name>");
                return 1;
            }
            env::env_info(&args[2])
        }
        Some(cmd) => {
            eprintln!("error: unknown env subcommand: {}", cmd);
            eprintln!("Usage: simple env [create|activate|list|remove|info] <name>");
            1
        }
        None => {
            print_env_help();
            0
        }
    }
}

fn print_env_help() {
    eprintln!("Simple Environment Management");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple env create <name>     Create new environment");
    eprintln!("  simple env activate <name>   Print activation script");
    eprintln!("  simple env list              List all environments");
    eprintln!("  simple env remove <name>     Remove environment");
    eprintln!("  simple env info <name>       Show environment info");
    eprintln!();
    eprintln!("To activate an environment:");
    eprintln!("  source $(simple env activate <name>)");
}

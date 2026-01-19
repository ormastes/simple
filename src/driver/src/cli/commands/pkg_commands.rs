//! Package management command handlers

use std::path::PathBuf;
use simple_pkg::commands::{add, cache_cmd, init, install, list, update};

/// Handle 'init' command - create new project
pub fn handle_init(args: &[String]) -> i32 {
    let name = args.get(1).map(|s| s.as_str());
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    match init::init_project(&dir, name) {
        Ok(()) => {
            println!(
                "Created new Simple project{}",
                name.map(|n| format!(" '{}'", n)).unwrap_or_default()
            );
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Handle 'add' command - add dependency
pub fn handle_add(args: &[String]) -> i32 {
    if args.len() < 2 {
        eprintln!("error: add requires a package name");
        eprintln!("Usage: simple add <pkg> [version] [--path <path>] [--git <url>] [--dev]");
        return 1;
    }
    let pkg_name = &args[1];
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    // Parse options
    let mut options = add::AddOptions::default();
    let mut i = 2;
    while i < args.len() {
        match args[i].as_str() {
            "--path" => {
                i += 1;
                if i < args.len() {
                    options.path = Some(args[i].clone());
                }
            }
            "--git" => {
                i += 1;
                if i < args.len() {
                    options.git = Some(args[i].clone());
                }
            }
            "--branch" => {
                i += 1;
                if i < args.len() {
                    options.branch = Some(args[i].clone());
                }
            }
            "--tag" => {
                i += 1;
                if i < args.len() {
                    options.tag = Some(args[i].clone());
                }
            }
            "--rev" => {
                i += 1;
                if i < args.len() {
                    options.rev = Some(args[i].clone());
                }
            }
            "--dev" => {
                options.dev = true;
            }
            arg if !arg.starts_with("-") && options.version.is_none() => {
                options.version = Some(arg.to_string());
            }
            _ => {}
        }
        i += 1;
    }

    match add::add_dependency(&dir, pkg_name, options) {
        Ok(()) => {
            println!("Added dependency '{}'", pkg_name);
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Handle 'remove' command - remove dependency
pub fn handle_remove(args: &[String]) -> i32 {
    if args.len() < 2 {
        eprintln!("error: remove requires a package name");
        eprintln!("Usage: simple remove <pkg> [--dev]");
        return 1;
    }
    let pkg_name = &args[1];
    let dev = args.iter().any(|a| a == "--dev");
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    match add::remove_dependency(&dir, pkg_name, dev) {
        Ok(true) => {
            println!("Removed dependency '{}'", pkg_name);
            0
        }
        Ok(false) => {
            eprintln!("error: dependency '{}' not found", pkg_name);
            1
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Handle 'install' command - install dependencies
pub fn handle_install() -> i32 {
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    match install::install_dependencies(&dir) {
        Ok(result) => {
            if result.installed == 0 && result.up_to_date == 0 && result.skipped == 0 {
                println!("No dependencies to install");
            } else {
                if result.installed > 0 {
                    println!("Installed {} package(s)", result.installed);
                }
                if result.up_to_date > 0 {
                    println!("{} package(s) up to date", result.up_to_date);
                }
                if result.skipped > 0 {
                    println!("{} package(s) skipped (git/registry not yet supported)", result.skipped);
                }
            }
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Handle 'update' command - update dependencies
pub fn handle_update(args: &[String]) -> i32 {
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    let pkg_name = args.get(1);

    let result = match pkg_name {
        Some(name) => update::update_package(&dir, name),
        None => update::update_all(&dir),
    };

    match result {
        Ok(r) => {
            if r.updated.is_empty() {
                println!("All dependencies up to date");
            } else {
                println!("Updated: {}", r.updated.join(", "));
            }
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Handle 'list' command - list dependencies
pub fn handle_list() -> i32 {
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    match list::list_dependencies(&dir) {
        Ok(packages) => {
            if packages.is_empty() {
                println!("No dependencies installed");
            } else {
                for pkg in packages {
                    let status = if pkg.is_linked { "" } else { " (not linked)" };
                    println!("{} ({}) [{}]{}", pkg.name, pkg.version, pkg.source_type, status);
                }
            }
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Handle 'tree' command - show dependency tree
pub fn handle_tree() -> i32 {
    let dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));

    match list::dependency_tree(&dir) {
        Ok(tree) => {
            // Print root
            println!("{} ({})", tree.name, tree.version);
            for (i, child) in tree.children.iter().enumerate() {
                let is_last = i == tree.children.len() - 1;
                print!("{}", list::format_tree(child, "", is_last));
            }
            0
        }
        Err(e) => {
            eprintln!("error: {}", e);
            1
        }
    }
}

/// Handle 'cache' command - manage package cache
pub fn handle_cache(args: &[String]) -> i32 {
    let subcommand = args.get(1).map(|s| s.as_str());

    match subcommand {
        Some("clean") => match cache_cmd::cache_clean() {
            Ok(size) => {
                println!("Cleaned {} from cache", cache_cmd::format_size(size));
                0
            }
            Err(e) => {
                eprintln!("error: {}", e);
                1
            }
        },
        Some("list") => match cache_cmd::cache_list() {
            Ok(packages) => {
                if packages.is_empty() {
                    println!("Cache is empty");
                } else {
                    for (name, version) in packages {
                        println!("{} ({})", name, version);
                    }
                }
                0
            }
            Err(e) => {
                eprintln!("error: {}", e);
                1
            }
        },
        Some("info") | None => match cache_cmd::cache_info() {
            Ok(info) => {
                println!("Cache location: {}", info.location.display());
                println!("Total size: {}", cache_cmd::format_size(info.size_bytes));
                println!("Packages: {}", info.package_count);
                println!("Git repos: {}", info.git_repo_count);
                0
            }
            Err(e) => {
                eprintln!("error: {}", e);
                1
            }
        },
        Some(cmd) => {
            eprintln!("error: unknown cache subcommand: {}", cmd);
            eprintln!("Usage: simple cache [info|list|clean]");
            1
        }
    }
}

//! WASM app packaging command handlers for VSCode and Electron.

use std::path::PathBuf;

use crate::cli::electron::{electron_build, electron_package, ElectronBuildOptions, ElectronPackageOptions};
use crate::cli::vscode::{
    vscode_build, vscode_package, vscode_publish, VsCodeBuildOptions, VsCodePackageOptions, VsCodePublishOptions,
};

pub fn handle_vscode(args: &[String]) -> i32 {
    if args.len() < 2 || args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print_vscode_help();
        return if args.len() < 2 { 1 } else { 0 };
    }

    match args[1].as_str() {
        "build" => handle_vscode_build(args),
        "package" => handle_vscode_package(args),
        "publish" => handle_vscode_publish(args),
        other => {
            eprintln!("error: unknown vscode subcommand '{}'", other);
            eprintln!("Available: build, package, publish");
            1
        }
    }
}

pub fn handle_electron(args: &[String]) -> i32 {
    if args.len() < 2 || args.iter().any(|arg| arg == "--help" || arg == "-h") {
        print_electron_help();
        return if args.len() < 2 { 1 } else { 0 };
    }

    match args[1].as_str() {
        "build" => handle_electron_build(args),
        "package" => handle_electron_package(args),
        other => {
            eprintln!("error: unknown electron subcommand '{}'", other);
            eprintln!("Available: build, package");
            1
        }
    }
}

fn handle_vscode_build(args: &[String]) -> i32 {
    let mut options = VsCodeBuildOptions::default();
    let mut source: Option<PathBuf> = None;
    let mut i = 2;

    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            "-o" | "--output" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: {} requires a value", arg);
                    return 1;
                };
                options.output_dir = PathBuf::from(value);
            }
            "--name" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --name requires a value");
                    return 1;
                };
                options.extension_name = value.clone();
            }
            "--display-name" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --display-name requires a value");
                    return 1;
                };
                options.display_name = value.clone();
            }
            "--version" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --version requires a value");
                    return 1;
                };
                options.version = value.clone();
            }
            "--publisher" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --publisher requires a value");
                    return 1;
                };
                options.publisher = value.clone();
            }
            "--description" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --description requires a value");
                    return 1;
                };
                options.description = value.clone();
            }
            "--optimize" | "--release" => {
                options.optimize = true;
            }
            _ if arg.starts_with("--output=") => {
                options.output_dir = PathBuf::from(arg.trim_start_matches("--output="));
            }
            _ if arg.starts_with("--name=") => {
                options.extension_name = arg.trim_start_matches("--name=").to_string();
            }
            _ if arg.starts_with("--display-name=") => {
                options.display_name = arg.trim_start_matches("--display-name=").to_string();
            }
            _ if arg.starts_with("--version=") => {
                options.version = arg.trim_start_matches("--version=").to_string();
            }
            _ if arg.starts_with("--publisher=") => {
                options.publisher = arg.trim_start_matches("--publisher=").to_string();
            }
            _ if arg.starts_with("--description=") => {
                options.description = arg.trim_start_matches("--description=").to_string();
            }
            _ if arg.starts_with('-') => {
                eprintln!("error: unknown option '{}'", arg);
                return 1;
            }
            _ if source.is_none() => {
                source = Some(PathBuf::from(arg));
            }
            _ => {
                eprintln!("error: unexpected positional argument '{}'", arg);
                return 1;
            }
        }
        i += 1;
    }

    let Some(source) = source else {
        eprintln!("error: vscode build requires a source file");
        eprintln!("Usage: simple vscode build <source.spl> [options]");
        return 1;
    };

    vscode_build(&source, options)
}

fn handle_vscode_package(args: &[String]) -> i32 {
    let mut options = VsCodePackageOptions::default();
    let mut i = 2;

    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            "--name" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --name requires a value");
                    return 1;
                };
                options.extension_name = value.clone();
            }
            "--version" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --version requires a value");
                    return 1;
                };
                options.version = value.clone();
            }
            _ if arg.starts_with("--name=") => {
                options.extension_name = arg.trim_start_matches("--name=").to_string();
            }
            _ if arg.starts_with("--version=") => {
                options.version = arg.trim_start_matches("--version=").to_string();
            }
            _ if arg.starts_with('-') => {
                eprintln!("error: unknown option '{}'", arg);
                return 1;
            }
            _ => {
                options.source_dir = PathBuf::from(arg);
            }
        }
        i += 1;
    }

    vscode_package(options)
}

fn handle_vscode_publish(args: &[String]) -> i32 {
    let mut vsix_path: Option<PathBuf> = None;
    let mut token = String::new();
    let mut i = 2;

    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            "--token" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --token requires a value");
                    return 1;
                };
                token = value.clone();
            }
            _ if arg.starts_with("--token=") => {
                token = arg.trim_start_matches("--token=").to_string();
            }
            _ if arg.starts_with('-') => {
                eprintln!("error: unknown option '{}'", arg);
                return 1;
            }
            _ if vsix_path.is_none() => {
                vsix_path = Some(PathBuf::from(arg));
            }
            _ => {
                eprintln!("error: unexpected positional argument '{}'", arg);
                return 1;
            }
        }
        i += 1;
    }

    let Some(vsix_path) = vsix_path else {
        eprintln!("error: vscode publish requires a .vsix path");
        eprintln!("Usage: simple vscode publish <extension.vsix> --token <PAT>");
        return 1;
    };

    let options = VsCodePublishOptions { vsix_path, token };
    vscode_publish(options)
}

fn handle_electron_build(args: &[String]) -> i32 {
    let mut options = ElectronBuildOptions::default();
    let mut source: Option<PathBuf> = None;
    let mut i = 2;

    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            "-o" | "--output" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: {} requires a value", arg);
                    return 1;
                };
                options.output_dir = PathBuf::from(value);
            }
            "--name" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --name requires a value");
                    return 1;
                };
                options.app_name = value.clone();
            }
            "--version" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --version requires a value");
                    return 1;
                };
                options.version = value.clone();
            }
            "--icon" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --icon requires a value");
                    return 1;
                };
                options.icon = Some(PathBuf::from(value));
            }
            "--optimize" | "--release" => {
                options.optimize = true;
            }
            _ if arg.starts_with("--output=") => {
                options.output_dir = PathBuf::from(arg.trim_start_matches("--output="));
            }
            _ if arg.starts_with("--name=") => {
                options.app_name = arg.trim_start_matches("--name=").to_string();
            }
            _ if arg.starts_with("--version=") => {
                options.version = arg.trim_start_matches("--version=").to_string();
            }
            _ if arg.starts_with("--icon=") => {
                options.icon = Some(PathBuf::from(arg.trim_start_matches("--icon=")));
            }
            _ if arg.starts_with('-') => {
                eprintln!("error: unknown option '{}'", arg);
                return 1;
            }
            _ if source.is_none() => {
                source = Some(PathBuf::from(arg));
            }
            _ => {
                eprintln!("error: unexpected positional argument '{}'", arg);
                return 1;
            }
        }
        i += 1;
    }

    let Some(source) = source else {
        eprintln!("error: electron build requires a source file");
        eprintln!("Usage: simple electron build <source.spl> [options]");
        return 1;
    };

    electron_build(&source, options)
}

fn handle_electron_package(args: &[String]) -> i32 {
    let mut options = ElectronPackageOptions::default();
    let mut i = 2;

    while i < args.len() {
        let arg = args[i].as_str();
        match arg {
            "--platform" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --platform requires a value");
                    return 1;
                };
                options.platforms = split_csv(value);
            }
            "--arch" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --arch requires a value");
                    return 1;
                };
                options.arch = split_csv(value);
            }
            "--name" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --name requires a value");
                    return 1;
                };
                options.app_name = value.clone();
            }
            "--version" => {
                i += 1;
                let Some(value) = args.get(i) else {
                    eprintln!("error: --version requires a value");
                    return 1;
                };
                options.version = value.clone();
            }
            _ if arg.starts_with("--platform=") => {
                options.platforms = split_csv(arg.trim_start_matches("--platform="));
            }
            _ if arg.starts_with("--arch=") => {
                options.arch = split_csv(arg.trim_start_matches("--arch="));
            }
            _ if arg.starts_with("--name=") => {
                options.app_name = arg.trim_start_matches("--name=").to_string();
            }
            _ if arg.starts_with("--version=") => {
                options.version = arg.trim_start_matches("--version=").to_string();
            }
            _ if arg.starts_with('-') => {
                eprintln!("error: unknown option '{}'", arg);
                return 1;
            }
            _ => {
                options.source_dir = PathBuf::from(arg);
            }
        }
        i += 1;
    }

    electron_package(options)
}

fn split_csv(value: &str) -> Vec<String> {
    value
        .split(',')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(ToOwned::to_owned)
        .collect()
}

fn print_vscode_help() {
    eprintln!("Simple VSCode Extension Tools");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple vscode build <source.spl> [options]     Build extension assets + WASM");
    eprintln!("  simple vscode package [dir] [options]          Package a built extension as .vsix");
    eprintln!("  simple vscode publish <file.vsix> --token <PAT>  Publish a .vsix to marketplace");
    eprintln!();
    eprintln!("Build options:");
    eprintln!("  -o, --output <dir>       Output directory (default: dist)");
    eprintln!("  --name <name>            Extension package name");
    eprintln!("  --display-name <name>    Marketplace display name");
    eprintln!("  --version <version>      Extension version");
    eprintln!("  --publisher <publisher>  Publisher ID");
    eprintln!("  --description <text>     Extension description");
    eprintln!("  --optimize, --release    Optimize the emitted WASM");
    eprintln!();
}

fn print_electron_help() {
    eprintln!("Simple Electron App Tools");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple electron build <source.spl> [options]  Build Electron assets + WASM");
    eprintln!("  simple electron package [dir] [options]       Package a built Electron app");
    eprintln!();
    eprintln!("Build options:");
    eprintln!("  -o, --output <dir>     Output directory (default: dist)");
    eprintln!("  --name <name>          Application name");
    eprintln!("  --version <version>    Application version");
    eprintln!("  --icon <path>          Application icon");
    eprintln!("  --optimize, --release  Optimize the emitted WASM");
    eprintln!();
    eprintln!("Package options:");
    eprintln!("  --platform <csv>       Target platforms: win, mac, linux, all");
    eprintln!("  --arch <csv>           Target architectures: x64, arm64, all");
    eprintln!();
}

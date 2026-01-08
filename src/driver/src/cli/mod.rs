//! CLI modules for the Simple language driver.

pub mod analysis;
pub mod audit;
pub mod basic;
pub mod code_quality;
pub mod compile;
pub mod electron;
pub mod gen_lean;
pub mod help;
pub mod init;
pub mod llm_tools;
pub mod repl;
pub mod sandbox;
pub mod test_discovery;
pub mod test_output;
pub mod test_runner;
#[cfg(feature = "tui")]
pub mod tui;
pub mod vscode;
pub mod web;

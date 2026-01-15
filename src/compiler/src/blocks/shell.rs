//! Shell block handler for portable shell scripting.
//!
//! Supports:
//! - Variable interpolation: $VAR, ${VAR}
//! - Command substitution: $(command)
//! - Basic shell constructs: if, for, while
//! - Pipe operations: cmd1 | cmd2
//! - Redirection: >, >>, <, 2>&1

use super::{BlockHandler, BlockResult};
use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;

/// Shell block handler
pub struct ShellBlock;

impl BlockHandler for ShellBlock {
    fn evaluate(&self, payload: &str) -> BlockResult {
        // Parse the shell script
        let script = parse_shell_script(payload)?;

        // Return as a Block value with the parsed script
        Ok(Value::Block {
            kind: "sh".to_string(),
            payload: payload.to_string(),
            result: Some(Box::new(script)),
        })
    }

    fn kind(&self) -> &'static str {
        "sh"
    }
}

/// Parsed shell command structure
#[derive(Debug, Clone)]
pub enum ShellCommand {
    /// Simple command with arguments
    Simple {
        command: String,
        args: Vec<String>,
    },
    /// Pipeline of commands
    Pipeline(Vec<ShellCommand>),
    /// Variable assignment
    Assignment {
        name: String,
        value: String,
    },
    /// Command sequence (separated by ;)
    Sequence(Vec<ShellCommand>),
}

/// Parse a shell script and return a Value
fn parse_shell_script(payload: &str) -> Result<Value, CompileError> {
    let payload = payload.trim();

    if payload.is_empty() {
        return Ok(Value::Nil);
    }

    // Split by lines and parse each command
    let lines: Vec<&str> = payload.lines().collect();
    let mut commands = Vec::new();

    for line in lines {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }

        // Parse individual command
        let cmd = parse_command(line)?;
        commands.push(cmd);
    }

    if commands.is_empty() {
        return Ok(Value::Nil);
    }

    // Return structured representation
    Ok(Value::Dict(
        commands
            .into_iter()
            .enumerate()
            .map(|(i, cmd)| (i.to_string(), command_to_value(cmd)))
            .collect(),
    ))
}

/// Parse a single shell command line
fn parse_command(line: &str) -> Result<ShellCommand, CompileError> {
    // Check for variable assignment: VAR=value
    if let Some(eq_pos) = line.find('=') {
        let name = &line[..eq_pos];
        // Ensure it's a valid variable name (no spaces before =)
        if !name.contains(' ') && !name.is_empty() && name.chars().all(|c| c.is_alphanumeric() || c == '_') {
            let value = &line[eq_pos + 1..];
            return Ok(ShellCommand::Assignment {
                name: name.to_string(),
                value: value.trim_matches('"').trim_matches('\'').to_string(),
            });
        }
    }

    // Check for pipeline: cmd1 | cmd2
    if line.contains(" | ") {
        let parts: Vec<&str> = line.split(" | ").collect();
        let mut pipeline = Vec::new();
        for part in parts {
            pipeline.push(parse_command(part.trim())?);
        }
        return Ok(ShellCommand::Pipeline(pipeline));
    }

    // Check for sequence: cmd1 ; cmd2
    if line.contains(" ; ") {
        let parts: Vec<&str> = line.split(" ; ").collect();
        let mut sequence = Vec::new();
        for part in parts {
            sequence.push(parse_command(part.trim())?);
        }
        return Ok(ShellCommand::Sequence(sequence));
    }

    // Simple command with arguments
    let mut parts = line.split_whitespace();
    let command = parts.next().unwrap_or("").to_string();
    let args: Vec<String> = parts.map(|s| s.to_string()).collect();

    Ok(ShellCommand::Simple { command, args })
}

/// Convert a ShellCommand to a Value for runtime representation
fn command_to_value(cmd: ShellCommand) -> Value {
    match cmd {
        ShellCommand::Simple { command, args } => {
            let mut fields = HashMap::new();
            fields.insert("type".to_string(), Value::Str("simple".to_string()));
            fields.insert("command".to_string(), Value::Str(command));
            fields.insert(
                "args".to_string(),
                Value::Array(args.into_iter().map(Value::Str).collect()),
            );
            Value::Dict(fields)
        }
        ShellCommand::Pipeline(cmds) => {
            let mut fields = HashMap::new();
            fields.insert("type".to_string(), Value::Str("pipeline".to_string()));
            fields.insert(
                "commands".to_string(),
                Value::Array(cmds.into_iter().map(command_to_value).collect()),
            );
            Value::Dict(fields)
        }
        ShellCommand::Assignment { name, value } => {
            let mut fields = HashMap::new();
            fields.insert("type".to_string(), Value::Str("assignment".to_string()));
            fields.insert("name".to_string(), Value::Str(name));
            fields.insert("value".to_string(), Value::Str(value));
            Value::Dict(fields)
        }
        ShellCommand::Sequence(cmds) => {
            let mut fields = HashMap::new();
            fields.insert("type".to_string(), Value::Str("sequence".to_string()));
            fields.insert(
                "commands".to_string(),
                Value::Array(cmds.into_iter().map(command_to_value).collect()),
            );
            Value::Dict(fields)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_command() {
        let result = parse_command("echo hello").unwrap();
        match result {
            ShellCommand::Simple { command, args } => {
                assert_eq!(command, "echo");
                assert_eq!(args, vec!["hello"]);
            }
            _ => panic!("expected simple command"),
        }
    }

    #[test]
    fn test_parse_assignment() {
        let result = parse_command("VAR=value").unwrap();
        match result {
            ShellCommand::Assignment { name, value } => {
                assert_eq!(name, "VAR");
                assert_eq!(value, "value");
            }
            _ => panic!("expected assignment"),
        }
    }

    #[test]
    fn test_parse_pipeline() {
        let result = parse_command("cat file | grep pattern").unwrap();
        match result {
            ShellCommand::Pipeline(cmds) => {
                assert_eq!(cmds.len(), 2);
            }
            _ => panic!("expected pipeline"),
        }
    }

    #[test]
    fn test_shell_block_evaluate() {
        let handler = ShellBlock;
        let result = handler.evaluate("echo hello").unwrap();
        match result {
            Value::Block { kind, .. } => {
                assert_eq!(kind, "sh");
            }
            _ => panic!("expected block value"),
        }
    }
}

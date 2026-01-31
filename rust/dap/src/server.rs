//! DAP server implementation
//!
//! Minimal Debug Adapter supporting:
//! - Initialize/launch/disconnect lifecycle
//! - Breakpoint management
//! - Stack trace inspection
//! - Step through code
//! - Variable inspection

use crate::protocol::*;
use crate::transport::{read_message, write_message, TransportError};
use std::collections::HashMap;
use std::io::{self, BufReader, BufWriter};

/// Breakpoint information
#[derive(Debug, Clone)]
struct BreakpointInfo {
    line: i64,
    verified: bool,
}

/// Debugging state
enum DebugState {
    NotStarted,
    Stopped { reason: String, line: i64 },
    Running,
    Terminated,
}

/// DAP server state
pub struct DapServer {
    /// Next sequence number
    seq: i64,
    /// Breakpoints by file path
    breakpoints: HashMap<String, Vec<BreakpointInfo>>,
    /// Current debug state
    state: DebugState,
    /// Program being debugged
    program: Option<String>,
    /// Lines start at 1 (vs 0)
    lines_start_at1: bool,
}

impl DapServer {
    /// Create new DAP server
    pub fn new() -> Self {
        Self {
            seq: 1,
            breakpoints: HashMap::new(),
            state: DebugState::NotStarted,
            program: None,
            lines_start_at1: true,
        }
    }

    /// Run the server (blocking)
    pub fn run(&mut self) -> Result<(), TransportError> {
        let stdin = io::stdin();
        let stdout = io::stdout();
        let mut reader = BufReader::new(stdin);
        let mut writer = BufWriter::new(stdout);

        loop {
            let message = read_message(&mut reader)?;

            match message {
                Message::Request(req) => {
                    let response = self.handle_request(&req);
                    write_message(&mut writer, &Message::Response(response))?;

                    // Send events after certain commands
                    match req.command.as_str() {
                        "launch" => {
                            // Send initialized event
                            self.send_event(&mut writer, "initialized", None)?;
                        }
                        "disconnect" => {
                            // Exit after sending response
                            break;
                        }
                        _ => {}
                    }
                }
                Message::Response(_) => {
                    // Ignore responses from client
                }
                Message::Event(_) => {
                    // Ignore events from client
                }
            }
        }

        Ok(())
    }

    /// Handle request message
    fn handle_request(&mut self, req: &RequestMessage) -> ResponseMessage {
        match req.command.as_str() {
            "initialize" => self.handle_initialize(req),
            "launch" => self.handle_launch(req),
            "setBreakpoints" => self.handle_set_breakpoints(req),
            "configurationDone" => self.handle_configuration_done(req),
            "threads" => self.handle_threads(req),
            "stackTrace" => self.handle_stack_trace(req),
            "scopes" => self.handle_scopes(req),
            "variables" => self.handle_variables(req),
            "continue" => self.handle_continue(req),
            "next" => self.handle_next(req),
            "stepIn" => self.handle_step_in(req),
            "stepOut" => self.handle_step_out(req),
            "pause" => self.handle_pause(req),
            "disconnect" => self.handle_disconnect(req),
            _ => ResponseMessage {
                seq: self.next_seq(),
                request_seq: req.seq,
                success: false,
                command: req.command.clone(),
                message: Some(format!("Unknown command: {}", req.command)),
                body: None,
            },
        }
    }

    /// Send event to client
    fn send_event<W: io::Write>(
        &mut self,
        writer: &mut W,
        event: &str,
        body: Option<serde_json::Value>,
    ) -> Result<(), TransportError> {
        let event_msg = EventMessage {
            seq: self.next_seq(),
            event: event.to_string(),
            body,
        };
        write_message(writer, &Message::Event(event_msg))
    }

    fn next_seq(&mut self) -> i64 {
        let seq = self.seq;
        self.seq += 1;
        seq
    }

    fn handle_initialize(&mut self, req: &RequestMessage) -> ResponseMessage {
        // Parse arguments
        if let Some(args) = &req.arguments {
            if let Ok(init_args) = serde_json::from_value::<InitializeRequestArguments>(args.clone()) {
                self.lines_start_at1 = init_args.lines_start_at1.unwrap_or(true);
            }
        }

        let capabilities = Capabilities {
            supports_configuration_done_request: Some(true),
            supports_breakpoint_locations_request: Some(false),
        };

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: serde_json::to_value(&capabilities).ok(),
        }
    }

    fn handle_launch(&mut self, req: &RequestMessage) -> ResponseMessage {
        // Parse launch arguments
        if let Some(args) = &req.arguments {
            if let Ok(launch_args) = serde_json::from_value::<LaunchRequestArguments>(args.clone()) {
                self.program = Some(launch_args.program.clone());

                // Set initial state
                if launch_args.stop_on_entry.unwrap_or(false) {
                    self.state = DebugState::Stopped {
                        reason: "entry".to_string(),
                        line: 1,
                    };
                } else {
                    self.state = DebugState::Running;
                }
            }
        }

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: None,
        }
    }

    fn handle_set_breakpoints(&mut self, req: &RequestMessage) -> ResponseMessage {
        let mut breakpoints = Vec::new();

        if let Some(args) = &req.arguments {
            if let Ok(bp_args) = serde_json::from_value::<SetBreakpointsArguments>(args.clone()) {
                let path = bp_args.source.path.unwrap_or_default();
                let mut bp_infos = Vec::new();

                if let Some(source_bps) = bp_args.breakpoints {
                    for bp in source_bps {
                        let bp_info = BreakpointInfo {
                            line: bp.line,
                            verified: true,
                        };
                        bp_infos.push(bp_info.clone());

                        breakpoints.push(Breakpoint {
                            verified: true,
                            line: Some(bp.line),
                            message: None,
                        });
                    }
                }

                self.breakpoints.insert(path, bp_infos);
            }
        }

        let body = SetBreakpointsResponseBody { breakpoints };

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: serde_json::to_value(&body).ok(),
        }
    }

    fn handle_configuration_done(&mut self, req: &RequestMessage) -> ResponseMessage {
        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: None,
        }
    }

    fn handle_threads(&mut self, req: &RequestMessage) -> ResponseMessage {
        let threads = vec![Thread {
            id: 1,
            name: "Main Thread".to_string(),
        }];

        let body = ThreadsResponseBody { threads };

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: serde_json::to_value(&body).ok(),
        }
    }

    fn handle_stack_trace(&mut self, req: &RequestMessage) -> ResponseMessage {
        // Minimal stack trace - just show current location
        let stack_frames = match &self.state {
            DebugState::Stopped { line, .. } => {
                vec![StackFrame {
                    id: 1,
                    name: "main".to_string(),
                    source: self.program.as_ref().map(|p| Source {
                        path: Some(p.clone()),
                        name: None,
                    }),
                    line: *line,
                    column: 1,
                }]
            }
            _ => vec![],
        };

        let body = StackTraceResponseBody { stack_frames };

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: serde_json::to_value(&body).ok(),
        }
    }

    fn handle_scopes(&mut self, req: &RequestMessage) -> ResponseMessage {
        let scopes = vec![Scope {
            name: "Locals".to_string(),
            variables_reference: 1,
            expensive: false,
        }];

        let body = ScopesResponseBody { scopes };

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: serde_json::to_value(&body).ok(),
        }
    }

    fn handle_variables(&mut self, req: &RequestMessage) -> ResponseMessage {
        // Minimal variable list
        let variables = vec![Variable {
            name: "x".to_string(),
            value: "42".to_string(),
            var_type: Some("int".to_string()),
            variables_reference: 0,
        }];

        let body = VariablesResponseBody { variables };

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: serde_json::to_value(&body).ok(),
        }
    }

    fn handle_continue(&mut self, req: &RequestMessage) -> ResponseMessage {
        self.state = DebugState::Running;

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: None,
        }
    }

    fn handle_next(&mut self, req: &RequestMessage) -> ResponseMessage {
        // Step over - simulate by staying stopped at next line
        if let DebugState::Stopped { line, .. } = &self.state {
            self.state = DebugState::Stopped {
                reason: "step".to_string(),
                line: line + 1,
            };
        }

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: None,
        }
    }

    fn handle_step_in(&mut self, req: &RequestMessage) -> ResponseMessage {
        // Step in - similar to next for minimal impl
        self.handle_next(req)
    }

    fn handle_step_out(&mut self, req: &RequestMessage) -> ResponseMessage {
        // Step out - similar to next for minimal impl
        self.handle_next(req)
    }

    fn handle_pause(&mut self, req: &RequestMessage) -> ResponseMessage {
        self.state = DebugState::Stopped {
            reason: "pause".to_string(),
            line: 1,
        };

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: None,
        }
    }

    fn handle_disconnect(&mut self, req: &RequestMessage) -> ResponseMessage {
        self.state = DebugState::Terminated;

        ResponseMessage {
            seq: self.next_seq(),
            request_seq: req.seq,
            success: true,
            command: req.command.clone(),
            message: None,
            body: None,
        }
    }
}

impl Default for DapServer {
    fn default() -> Self {
        Self::new()
    }
}

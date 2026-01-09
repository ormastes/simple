//! TUI (Terminal User Interface) Renderer
//!
//! Renders SUI templates to the terminal using crossterm.

use crate::ir::NodeId;
use crate::patchset::PatchOp;
use crate::render::RenderBackend;
use crossterm::cursor::{Hide, MoveTo, Show};
use crossterm::event::{Event, KeyCode, KeyEvent, MouseEvent};
use crossterm::style::{
    Attribute as TermAttr, Color, ResetColor, SetAttribute, SetBackgroundColor, SetForegroundColor,
};
use crossterm::terminal::{self, Clear, ClearType};
use crossterm::{execute, queue};
use std::collections::HashMap;
use std::io::{self, Stdout, Write};
use thiserror::Error;

/// TUI renderer error
#[derive(Debug, Error)]
pub enum TuiError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("Node not found: {0:?}")]
    NodeNotFound(NodeId),
    #[error("Invalid operation: {0}")]
    InvalidOperation(String),
}

/// TUI node type
#[derive(Debug, Clone)]
pub struct TuiNode {
    pub id: NodeId,
    pub kind: TuiNodeKind,
    pub children: Vec<NodeId>,
    pub parent: Option<NodeId>,
    pub attrs: HashMap<String, String>,
    pub layout: Layout,
}

/// Kind of TUI node
#[derive(Debug, Clone)]
pub enum TuiNodeKind {
    /// Root container
    Root,
    /// Box container (div)
    Box,
    /// Text span
    Text(String),
    /// Button
    Button { label: String, focused: bool },
    /// Input field
    Input {
        value: String,
        cursor: usize,
        focused: bool,
    },
    /// List container
    List,
    /// List item
    ListItem { bullet: char },
    /// Table
    Table { columns: usize },
    /// Table row
    TableRow,
    /// Table cell
    TableCell,
}

/// Layout information for a node
#[derive(Debug, Clone, Default)]
pub struct Layout {
    pub x: u16,
    pub y: u16,
    pub width: u16,
    pub height: u16,
}

/// TUI theme configuration
#[derive(Debug, Clone)]
pub struct TuiTheme {
    pub text_color: Color,
    pub bg_color: Color,
    pub border_color: Color,
    pub focus_color: Color,
    pub button_color: Color,
    pub input_color: Color,
    pub border_style: BorderStyle,
}

impl Default for TuiTheme {
    fn default() -> Self {
        Self {
            text_color: Color::White,
            bg_color: Color::Black,
            border_color: Color::DarkGrey,
            focus_color: Color::Cyan,
            button_color: Color::Blue,
            input_color: Color::Green,
            border_style: BorderStyle::Single,
        }
    }
}

/// Border drawing style
#[derive(Debug, Clone, Copy, Default)]
pub enum BorderStyle {
    #[default]
    Single,
    Double,
    Rounded,
    None,
}

impl BorderStyle {
    pub fn chars(&self) -> BorderChars {
        match self {
            BorderStyle::Single => BorderChars {
                top_left: '┌',
                top_right: '┐',
                bottom_left: '└',
                bottom_right: '┘',
                horizontal: '─',
                vertical: '│',
            },
            BorderStyle::Double => BorderChars {
                top_left: '╔',
                top_right: '╗',
                bottom_left: '╚',
                bottom_right: '╝',
                horizontal: '═',
                vertical: '║',
            },
            BorderStyle::Rounded => BorderChars {
                top_left: '╭',
                top_right: '╮',
                bottom_left: '╰',
                bottom_right: '╯',
                horizontal: '─',
                vertical: '│',
            },
            BorderStyle::None => BorderChars {
                top_left: ' ',
                top_right: ' ',
                bottom_left: ' ',
                bottom_right: ' ',
                horizontal: ' ',
                vertical: ' ',
            },
        }
    }
}

/// Border drawing characters
pub struct BorderChars {
    pub top_left: char,
    pub top_right: char,
    pub bottom_left: char,
    pub bottom_right: char,
    pub horizontal: char,
    pub vertical: char,
}

/// TUI rendering context
pub struct TuiContext {
    pub nodes: HashMap<NodeId, TuiNode>,
    pub root: NodeId,
    pub focus: Option<NodeId>,
    pub focus_order: Vec<NodeId>,
    next_id: u64,
}

impl TuiContext {
    pub fn new() -> Self {
        let root_id = NodeId(0);
        let mut nodes = HashMap::new();
        nodes.insert(
            root_id,
            TuiNode {
                id: root_id,
                kind: TuiNodeKind::Root,
                children: Vec::new(),
                parent: None,
                attrs: HashMap::new(),
                layout: Layout::default(),
            },
        );
        Self {
            nodes,
            root: root_id,
            focus: None,
            focus_order: Vec::new(),
            next_id: 1,
        }
    }

    pub fn alloc_id(&mut self) -> NodeId {
        let id = NodeId(self.next_id);
        self.next_id += 1;
        id
    }

    pub fn focus_next(&mut self) {
        if self.focus_order.is_empty() {
            return;
        }
        match self.focus {
            Some(current) => {
                if let Some(idx) = self.focus_order.iter().position(|&id| id == current) {
                    let next_idx = (idx + 1) % self.focus_order.len();
                    self.focus = Some(self.focus_order[next_idx]);
                }
            }
            None => {
                self.focus = self.focus_order.first().copied();
            }
        }
    }

    pub fn focus_prev(&mut self) {
        if self.focus_order.is_empty() {
            return;
        }
        match self.focus {
            Some(current) => {
                if let Some(idx) = self.focus_order.iter().position(|&id| id == current) {
                    let prev_idx = if idx == 0 {
                        self.focus_order.len() - 1
                    } else {
                        idx - 1
                    };
                    self.focus = Some(self.focus_order[prev_idx]);
                }
            }
            None => {
                self.focus = self.focus_order.last().copied();
            }
        }
    }
}

impl Default for TuiContext {
    fn default() -> Self {
        Self::new()
    }
}

/// TUI renderer
pub struct TuiRenderer {
    pub theme: TuiTheme,
    stdout: Stdout,
}

impl TuiRenderer {
    pub fn new() -> Self {
        Self {
            theme: TuiTheme::default(),
            stdout: io::stdout(),
        }
    }

    pub fn with_theme(theme: TuiTheme) -> Self {
        Self {
            theme,
            stdout: io::stdout(),
        }
    }

    /// Initialize terminal for TUI mode
    pub fn init(&mut self) -> Result<(), TuiError> {
        terminal::enable_raw_mode()?;
        execute!(self.stdout, Hide, Clear(ClearType::All))?;
        Ok(())
    }

    /// Restore terminal to normal mode
    pub fn cleanup(&mut self) -> Result<(), TuiError> {
        execute!(self.stdout, Show, ResetColor, Clear(ClearType::All))?;
        terminal::disable_raw_mode()?;
        Ok(())
    }

    /// Render the entire tree to the terminal
    pub fn render(&mut self, ctx: &TuiContext) -> Result<(), TuiError> {
        execute!(self.stdout, Clear(ClearType::All), MoveTo(0, 0))?;
        self.render_node(ctx, ctx.root, 0, 0)?;
        self.stdout.flush()?;
        Ok(())
    }

    /// Render a single node and its children
    fn render_node(
        &mut self,
        ctx: &TuiContext,
        node_id: NodeId,
        x: u16,
        y: u16,
    ) -> Result<(u16, u16), TuiError> {
        let node = ctx
            .nodes
            .get(&node_id)
            .ok_or(TuiError::NodeNotFound(node_id))?;
        let is_focused = ctx.focus == Some(node_id);

        match &node.kind {
            TuiNodeKind::Root => {
                let mut current_y = y;
                for &child_id in &node.children {
                    let (_, h) = self.render_node(ctx, child_id, x, current_y)?;
                    current_y += h;
                }
                Ok((0, current_y - y))
            }
            TuiNodeKind::Box => {
                let border = self.theme.border_style.chars();
                let width = node.layout.width.max(10);
                let has_border = node.attrs.get("border").map_or(false, |v| v != "none");

                if has_border {
                    // Draw border
                    let color = if is_focused {
                        self.theme.focus_color
                    } else {
                        self.theme.border_color
                    };
                    queue!(self.stdout, MoveTo(x, y), SetForegroundColor(color))?;
                    write!(self.stdout, "{}", border.top_left)?;
                    for _ in 0..width.saturating_sub(2) {
                        write!(self.stdout, "{}", border.horizontal)?;
                    }
                    write!(self.stdout, "{}", border.top_right)?;
                }

                // Render children
                let mut current_y = if has_border { y + 1 } else { y };
                let child_x = if has_border { x + 1 } else { x };

                for &child_id in &node.children {
                    if has_border {
                        queue!(self.stdout, MoveTo(x, current_y))?;
                        write!(self.stdout, "{}", border.vertical)?;
                    }
                    let (_, h) = self.render_node(ctx, child_id, child_x, current_y)?;
                    if has_border {
                        queue!(self.stdout, MoveTo(x + width - 1, current_y))?;
                        write!(self.stdout, "{}", border.vertical)?;
                    }
                    current_y += h.max(1);
                }

                if has_border {
                    queue!(self.stdout, MoveTo(x, current_y))?;
                    write!(self.stdout, "{}", border.bottom_left)?;
                    for _ in 0..width.saturating_sub(2) {
                        write!(self.stdout, "{}", border.horizontal)?;
                    }
                    write!(self.stdout, "{}", border.bottom_right)?;
                    current_y += 1;
                }

                queue!(self.stdout, ResetColor)?;
                Ok((width, current_y - y))
            }
            TuiNodeKind::Text(content) => {
                queue!(
                    self.stdout,
                    MoveTo(x, y),
                    SetForegroundColor(self.theme.text_color)
                )?;
                write!(self.stdout, "{}", content)?;
                queue!(self.stdout, ResetColor)?;
                Ok((content.len() as u16, 1))
            }
            TuiNodeKind::Button { label, focused: _ } => {
                let color = if is_focused {
                    self.theme.focus_color
                } else {
                    self.theme.button_color
                };
                queue!(self.stdout, MoveTo(x, y), SetForegroundColor(color))?;
                if is_focused {
                    queue!(self.stdout, SetAttribute(TermAttr::Reverse))?;
                }
                write!(self.stdout, "[ {} ]", label)?;
                queue!(self.stdout, SetAttribute(TermAttr::Reset), ResetColor)?;
                Ok((label.len() as u16 + 4, 1))
            }
            TuiNodeKind::Input {
                value,
                cursor,
                focused: _,
            } => {
                let width = node.layout.width.max(10);
                let color = if is_focused {
                    self.theme.focus_color
                } else {
                    self.theme.input_color
                };
                queue!(self.stdout, MoveTo(x, y), SetForegroundColor(color))?;
                write!(self.stdout, "[")?;

                let display_value = if value.len() > (width - 2) as usize {
                    &value[value.len() - (width - 2) as usize..]
                } else {
                    value
                };
                write!(self.stdout, "{}", display_value)?;

                let padding = (width - 2) as usize - display_value.len();
                for _ in 0..padding {
                    write!(self.stdout, "_")?;
                }
                write!(self.stdout, "]")?;

                if is_focused {
                    let cursor_pos =
                        (x + 1 + (*cursor).min(display_value.len()) as u16).min(x + width - 2);
                    queue!(self.stdout, MoveTo(cursor_pos, y))?;
                }

                queue!(self.stdout, ResetColor)?;
                Ok((width, 1))
            }
            TuiNodeKind::List => {
                let mut current_y = y;
                for &child_id in &node.children {
                    let (_, h) = self.render_node(ctx, child_id, x, current_y)?;
                    current_y += h;
                }
                Ok((0, current_y - y))
            }
            TuiNodeKind::ListItem { bullet } => {
                queue!(
                    self.stdout,
                    MoveTo(x, y),
                    SetForegroundColor(self.theme.text_color)
                )?;
                write!(self.stdout, "{} ", bullet)?;
                let mut width = 2u16;
                for &child_id in &node.children {
                    let (w, _) = self.render_node(ctx, child_id, x + width, y)?;
                    width += w;
                }
                queue!(self.stdout, ResetColor)?;
                Ok((width, 1))
            }
            TuiNodeKind::Table { columns: _ } | TuiNodeKind::TableRow | TuiNodeKind::TableCell => {
                // Simplified table rendering
                let mut current_y = y;
                for &child_id in &node.children {
                    let (_, h) = self.render_node(ctx, child_id, x, current_y)?;
                    current_y += h;
                }
                Ok((0, current_y - y))
            }
        }
    }

    /// Handle keyboard input
    pub fn handle_key(&mut self, ctx: &mut TuiContext, event: KeyEvent) -> bool {
        match event.code {
            KeyCode::Tab => {
                ctx.focus_next();
                true
            }
            KeyCode::BackTab => {
                ctx.focus_prev();
                true
            }
            KeyCode::Char(c) => {
                if let Some(focus_id) = ctx.focus {
                    if let Some(node) = ctx.nodes.get_mut(&focus_id) {
                        if let TuiNodeKind::Input { value, cursor, .. } = &mut node.kind {
                            value.insert(*cursor, c);
                            *cursor += 1;
                            return true;
                        }
                    }
                }
                false
            }
            KeyCode::Backspace => {
                if let Some(focus_id) = ctx.focus {
                    if let Some(node) = ctx.nodes.get_mut(&focus_id) {
                        if let TuiNodeKind::Input { value, cursor, .. } = &mut node.kind {
                            if *cursor > 0 {
                                *cursor -= 1;
                                value.remove(*cursor);
                                return true;
                            }
                        }
                    }
                }
                false
            }
            KeyCode::Left => {
                if let Some(focus_id) = ctx.focus {
                    if let Some(node) = ctx.nodes.get_mut(&focus_id) {
                        if let TuiNodeKind::Input { cursor, .. } = &mut node.kind {
                            if *cursor > 0 {
                                *cursor -= 1;
                                return true;
                            }
                        }
                    }
                }
                false
            }
            KeyCode::Right => {
                if let Some(focus_id) = ctx.focus {
                    if let Some(node) = ctx.nodes.get_mut(&focus_id) {
                        if let TuiNodeKind::Input { value, cursor, .. } = &mut node.kind {
                            if *cursor < value.len() {
                                *cursor += 1;
                                return true;
                            }
                        }
                    }
                }
                false
            }
            _ => false,
        }
    }
}

impl Default for TuiRenderer {
    fn default() -> Self {
        Self::new()
    }
}

impl RenderBackend for TuiRenderer {
    type Node = TuiNode;
    type Context = TuiContext;
    type Error = TuiError;

    fn create_element(
        &mut self,
        ctx: &mut Self::Context,
        tag: &str,
    ) -> Result<Self::Node, Self::Error> {
        let id = ctx.alloc_id();
        let kind = match tag {
            "div" | "section" | "article" | "main" | "header" | "footer" | "nav" => {
                TuiNodeKind::Box
            }
            "span" | "p" | "h1" | "h2" | "h3" | "h4" | "h5" | "h6" => {
                TuiNodeKind::Text(String::new())
            }
            "button" => TuiNodeKind::Button {
                label: String::new(),
                focused: false,
            },
            "input" => TuiNodeKind::Input {
                value: String::new(),
                cursor: 0,
                focused: false,
            },
            "ul" | "ol" => TuiNodeKind::List,
            "li" => TuiNodeKind::ListItem { bullet: '•' },
            "table" => TuiNodeKind::Table { columns: 0 },
            "tr" => TuiNodeKind::TableRow,
            "td" | "th" => TuiNodeKind::TableCell,
            _ => TuiNodeKind::Box,
        };

        let node = TuiNode {
            id,
            kind,
            children: Vec::new(),
            parent: None,
            attrs: HashMap::new(),
            layout: Layout::default(),
        };

        Ok(node)
    }

    fn create_text(
        &mut self,
        ctx: &mut Self::Context,
        text: &str,
    ) -> Result<Self::Node, Self::Error> {
        let id = ctx.alloc_id();
        Ok(TuiNode {
            id,
            kind: TuiNodeKind::Text(text.to_string()),
            children: Vec::new(),
            parent: None,
            attrs: HashMap::new(),
            layout: Layout::default(),
        })
    }

    fn set_attr(
        &mut self,
        node: &mut Self::Node,
        name: &str,
        value: &str,
    ) -> Result<(), Self::Error> {
        node.attrs.insert(name.to_string(), value.to_string());
        Ok(())
    }

    fn remove_attr(&mut self, node: &mut Self::Node, name: &str) -> Result<(), Self::Error> {
        node.attrs.remove(name);
        Ok(())
    }

    fn set_text(&mut self, node: &mut Self::Node, text: &str) -> Result<(), Self::Error> {
        node.kind = TuiNodeKind::Text(text.to_string());
        Ok(())
    }

    fn append_child(
        &mut self,
        parent: &mut Self::Node,
        child: Self::Node,
    ) -> Result<(), Self::Error> {
        parent.children.push(child.id);
        Ok(())
    }

    fn insert_child(
        &mut self,
        parent: &mut Self::Node,
        index: usize,
        child: Self::Node,
    ) -> Result<(), Self::Error> {
        let idx = index.min(parent.children.len());
        parent.children.insert(idx, child.id);
        Ok(())
    }

    fn remove_child(
        &mut self,
        parent: &mut Self::Node,
        child: &Self::Node,
    ) -> Result<(), Self::Error> {
        parent.children.retain(|&id| id != child.id);
        Ok(())
    }

    fn apply_patch(&mut self, ctx: &mut Self::Context, patch: &PatchOp) -> Result<(), Self::Error> {
        match patch {
            PatchOp::SetText { node_id, text } => {
                if let Some(node) = ctx.nodes.get_mut(node_id) {
                    node.kind = TuiNodeKind::Text(text.clone());
                }
            }
            PatchOp::SetAttr {
                node_id,
                name,
                value,
            } => {
                if let Some(node) = ctx.nodes.get_mut(node_id) {
                    node.attrs.insert(name.clone(), value.clone());
                }
            }
            PatchOp::RemoveAttr { node_id, name } => {
                if let Some(node) = ctx.nodes.get_mut(node_id) {
                    node.attrs.remove(name);
                }
            }
            PatchOp::RemoveChild {
                parent_id,
                child_id,
            } => {
                if let Some(parent) = ctx.nodes.get_mut(parent_id) {
                    parent.children.retain(|&id| id != *child_id);
                }
                ctx.nodes.remove(child_id);
            }
            _ => {}
        }
        Ok(())
    }

    fn get_node<'a>(&self, ctx: &'a Self::Context, id: NodeId) -> Option<&'a Self::Node> {
        ctx.nodes.get(&id)
    }

    fn get_node_mut<'a>(
        &mut self,
        ctx: &'a mut Self::Context,
        id: NodeId,
    ) -> Option<&'a mut Self::Node> {
        ctx.nodes.get_mut(&id)
    }
}

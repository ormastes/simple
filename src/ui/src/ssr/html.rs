//! HTML string rendering for SSR

use crate::parser::{AttributeValue, ControlNode, Element, SuiTemplate, TemplateNode};
use std::fmt::Write;

/// Render a template to an HTML string
pub fn render_to_html(template: &SuiTemplate) -> String {
    let mut output = String::new();
    for node in &template.content {
        render_node(&mut output, node);
    }
    output
}

fn render_node(output: &mut String, node: &TemplateNode) {
    match node {
        TemplateNode::Element(el) => render_element(output, el),
        TemplateNode::Text(text) => {
            output.push_str(&html_escape(&text.content));
        }
        TemplateNode::Output(out) => {
            // For SSR, we'd evaluate the expression here
            // For now, just output a placeholder
            let _ = write!(output, "<!-- output: {:?} -->", out.expr);
        }
        TemplateNode::RawOutput(out) => {
            let _ = write!(output, "<!-- raw: {:?} -->", out.expr);
        }
        TemplateNode::Control(ctrl) => render_control(output, ctrl),
        TemplateNode::Embed(embed) => {
            let _ = write!(output, "<!-- embed: {} -->", embed.component);
        }
        TemplateNode::Slot(slot) => {
            let _ = write!(output, "<!-- slot: {} -->", slot.name);
        }
        TemplateNode::Fill(fill) => {
            for child in &fill.content {
                render_node(output, child);
            }
        }
        TemplateNode::Comment(comment) => {
            let _ = write!(output, "<!-- {} -->", comment);
        }
    }
}

fn render_element(output: &mut String, el: &Element) {
    // Opening tag
    let _ = write!(output, "<{}", el.tag);

    // Attributes
    for attr in &el.attrs {
        match &attr.value {
            AttributeValue::Static(val) => {
                let _ = write!(output, " {}=\"{}\"", attr.name, html_escape_attr(val));
            }
            AttributeValue::Dynamic(_) => {
                // Skip dynamic attributes for now
            }
            AttributeValue::Boolean => {
                let _ = write!(output, " {}", attr.name);
            }
            AttributeValue::ConditionalClass { .. } => {
                // Skip conditional classes for now
            }
            AttributeValue::Event { .. } => {
                // Skip event handlers for now
            }
        }
    }

    if el.self_closing {
        output.push_str(" />");
        return;
    }

    output.push('>');

    // Children
    for child in &el.children {
        render_node(output, child);
    }

    // Closing tag
    let _ = write!(output, "</{}>", el.tag);
}

fn render_control(output: &mut String, ctrl: &ControlNode) {
    match ctrl {
        ControlNode::If(if_node) => {
            // For SSR, we'd evaluate the condition here
            // For now, render then branch
            for node in &if_node.then_branch {
                render_node(output, node);
            }
        }
        ControlNode::For(for_node) => {
            // For SSR, we'd iterate here
            // For now, just mark the loop
            let _ = write!(
                output,
                "<!-- for {} in {:?} -->",
                for_node.binding, for_node.iterable
            );
            for node in &for_node.body {
                render_node(output, node);
            }
            output.push_str("<!-- end for -->");
        }
        ControlNode::Let(_) => {
            // Let bindings don't produce output
        }
    }
}

fn html_escape(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for ch in s.chars() {
        match ch {
            '&' => result.push_str("&amp;"),
            '<' => result.push_str("&lt;"),
            '>' => result.push_str("&gt;"),
            '"' => result.push_str("&quot;"),
            '\'' => result.push_str("&#x27;"),
            _ => result.push(ch),
        }
    }
    result
}

fn html_escape_attr(s: &str) -> String {
    html_escape(s)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::SuiParser;

    #[test]
    fn test_simple_render() {
        let source = r#"{@ component Test @}
<div class="hello">World</div>"#;
        let mut parser = SuiParser::new(source);
        let template = parser.parse().unwrap();
        let html = render_to_html(&template);
        assert!(html.contains("<div class=\"hello\">"));
        assert!(html.contains("World"));
        assert!(html.contains("</div>"));
    }
}

use super::*;

fn parse(source: &str) -> Result<SuiTemplate, ParseError> {
    let mut parser = SuiParser::new(source);
    parser.parse()
}

#[test]
fn test_simple_component() {
    let source = r#"{@ component Counter @}
{$ let count: i32 $}
<div>{{ count }}</div>"#;

    let template = parse(source).unwrap();
    assert_eq!(template.kind, TemplateKind::Component);
    assert_eq!(template.name, "Counter");
    assert_eq!(template.declarations.len(), 1);
    assert_eq!(template.declarations[0].name, "count");
}

#[test]
fn test_if_control() {
    let source = r#"{@ component Test @}
{% if x > 0: %}
<span>positive</span>
{% else: %}
<span>not positive</span>
{% end %}"#;

    let template = parse(source).unwrap();
    // Find the If control node (may have whitespace nodes before it)
    let if_node = template
        .content
        .iter()
        .find_map(|n| {
            if let TemplateNode::Control(ControlNode::If(if_node)) = n {
                Some(if_node)
            } else {
                None
            }
        })
        .expect("Expected If control node");

    // Find span element in then branch
    let has_span_in_then = if_node.then_branch.iter().any(|n| {
        matches!(n, TemplateNode::Element(el) if el.tag == "span")
    });
    assert!(has_span_in_then, "Expected span in then branch");
    assert!(if_node.else_branch.is_some());
}

#[test]
fn test_for_control() {
    let source = r#"{@ component Test @}
{% for item in items: %}
<li>{{ item.name }}</li>
{% end %}"#;

    let template = parse(source).unwrap();
    // Find the For control node
    let for_node = template
        .content
        .iter()
        .find_map(|n| {
            if let TemplateNode::Control(ControlNode::For(for_node)) = n {
                Some(for_node)
            } else {
                None
            }
        })
        .expect("Expected For control node");
    assert_eq!(for_node.binding, "item");
}

#[test]
fn test_element_with_attrs() {
    let source = r#"{@ component Test @}
<button id="btn" class="primary" disabled>Click</button>"#;

    let template = parse(source).unwrap();
    // Find the button element
    let button = template
        .content
        .iter()
        .find_map(|n| {
            if let TemplateNode::Element(el) = n {
                if el.tag == "button" {
                    return Some(el);
                }
            }
            None
        })
        .expect("Expected button Element node");
    assert_eq!(button.tag, "button");
    assert_eq!(button.attrs.len(), 3);
}

#[test]
fn test_server_block() {
    let source = r#"{@ page Home @}
{- count = 42 -}"#;

    let template = parse(source).unwrap();
    assert!(template.server_block.is_some());
    let server = template.server_block.unwrap();
    assert_eq!(server.statements.len(), 1);
}

#[test]
fn test_client_block() {
    let source = r##"{@ component Counter @}
{+ on_click("#btn", handler) +}"##;

    let template = parse(source).unwrap();
    assert!(template.client_block.is_some());
}

#[test]
fn test_embed() {
    let source = r#"{@ page Home @}
{@ embed UserList users=users hydrate="visible" @}"#;

    let template = parse(source).unwrap();
    // Find the embed node
    let embed = template
        .content
        .iter()
        .find_map(|n| {
            if let TemplateNode::Embed(embed) = n {
                Some(embed)
            } else {
                None
            }
        })
        .expect("Expected Embed node");
    assert_eq!(embed.component, "UserList");
    assert_eq!(embed.hydrate, HydrateStrategy::Visible);
}

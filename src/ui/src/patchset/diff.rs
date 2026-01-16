//! Keyed diffing algorithm for efficient updates

use crate::ir::NodeId;
use crate::patchset::{PatchOp, PatchSet, Subtree, SubtreeNode};
use std::collections::HashMap;

/// A snapshot of a child node for diffing
#[derive(Debug, Clone)]
pub struct ChildSnapshot {
    /// Optional key for stable identity
    pub key: Option<String>,
    /// Node ID
    pub id: NodeId,
    /// Tag name (for elements)
    pub tag: Option<String>,
    /// Text content (for text nodes)
    pub text: Option<String>,
}

/// Diff two lists of children and produce patch operations
pub fn diff_children(parent_id: NodeId, old: &[ChildSnapshot], new: &[ChildSnapshot]) -> PatchSet {
    let mut patches = PatchSet::new();

    // Build key→index map for old children
    let old_key_map: HashMap<&str, usize> = old
        .iter()
        .enumerate()
        .filter_map(|(i, c)| c.key.as_ref().map(|k| (k.as_str(), i)))
        .collect();

    // Track which old children are still used
    let mut used_old: Vec<bool> = vec![false; old.len()];

    // Track insertions and moves
    let mut new_order: Vec<Option<usize>> = Vec::with_capacity(new.len());

    // First pass: match by key
    for new_child in new.iter() {
        if let Some(key) = &new_child.key {
            if let Some(&old_idx) = old_key_map.get(key.as_str()) {
                used_old[old_idx] = true;
                new_order.push(Some(old_idx));
                continue;
            }
        }
        new_order.push(None);
    }

    // Second pass: match unkeyed by position
    let mut unkeyed_old: Vec<usize> = old
        .iter()
        .enumerate()
        .filter(|(i, c)| c.key.is_none() && !used_old[*i])
        .map(|(i, _)| i)
        .collect();

    for (new_idx, slot) in new_order.iter_mut().enumerate() {
        if slot.is_none() && new[new_idx].key.is_none() {
            if let Some(old_idx) = unkeyed_old.pop() {
                used_old[old_idx] = true;
                *slot = Some(old_idx);
            }
        }
    }

    // Remove unused old children (in reverse order to preserve indices)
    for (old_idx, child) in old.iter().enumerate().rev() {
        if !used_old[old_idx] {
            patches.push(PatchOp::RemoveChild {
                parent_id,
                child_id: child.id,
            });
        }
    }

    // Insert new children and compute moves
    // Using a simple O(n) algorithm for now
    // TODO: [ui][P1] Implement LIS for optimal moves
    let mut current_pos = 0;
    for (new_idx, new_child) in new.iter().enumerate() {
        match new_order[new_idx] {
            Some(old_idx) => {
                // Child exists, check if it needs to move
                // For simplicity, we'll just track position
                let expected_pos = old
                    .iter()
                    .take(old_idx)
                    .filter(|c| used_old[old.iter().position(|x| x.id == c.id).unwrap()])
                    .count();
                if expected_pos != current_pos {
                    patches.push(PatchOp::MoveChild {
                        parent_id,
                        from_idx: expected_pos,
                        to_idx: new_idx,
                    });
                }
                current_pos = new_idx + 1;
            }
            None => {
                // New child, insert it
                let subtree = snapshot_to_subtree(new_child);
                patches.push(PatchOp::InsertChild {
                    parent_id,
                    index: new_idx,
                    subtree,
                });
            }
        }
    }

    patches
}

/// Convert a snapshot to a subtree for insertion
fn snapshot_to_subtree(snapshot: &ChildSnapshot) -> Subtree {
    if let Some(text) = &snapshot.text {
        Subtree::text(text)
    } else if let Some(tag) = &snapshot.tag {
        Subtree::element(tag, Vec::new(), Vec::new())
    } else {
        Subtree::text("")
    }
}

/// Diff two text values
pub fn diff_text(node_id: NodeId, old: &str, new: &str) -> Option<PatchOp> {
    if old != new {
        Some(PatchOp::SetText {
            node_id,
            text: new.to_string(),
        })
    } else {
        None
    }
}

/// Diff two attribute maps
pub fn diff_attrs(node_id: NodeId, old: &[(String, String)], new: &[(String, String)]) -> Vec<PatchOp> {
    let mut patches = Vec::new();

    let old_map: HashMap<&str, &str> = old.iter().map(|(k, v)| (k.as_str(), v.as_str())).collect();
    let new_map: HashMap<&str, &str> = new.iter().map(|(k, v)| (k.as_str(), v.as_str())).collect();

    // Find removed and changed attrs
    for (key, old_val) in &old_map {
        match new_map.get(key) {
            Some(new_val) if new_val != old_val => {
                patches.push(PatchOp::SetAttr {
                    node_id,
                    name: key.to_string(),
                    value: new_val.to_string(),
                });
            }
            None => {
                patches.push(PatchOp::RemoveAttr {
                    node_id,
                    name: key.to_string(),
                });
            }
            _ => {}
        }
    }

    // Find added attrs
    for (key, val) in &new_map {
        if !old_map.contains_key(key) {
            patches.push(PatchOp::SetAttr {
                node_id,
                name: key.to_string(),
                value: val.to_string(),
            });
        }
    }

    patches
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_child(id: u64, key: Option<&str>) -> ChildSnapshot {
        ChildSnapshot {
            key: key.map(String::from),
            id: NodeId(id),
            tag: Some("div".to_string()),
            text: None,
        }
    }

    #[test]
    fn test_diff_no_changes() {
        let old = vec![make_child(1, Some("a")), make_child(2, Some("b"))];
        let new = vec![make_child(1, Some("a")), make_child(2, Some("b"))];
        let patches = diff_children(NodeId(0), &old, &new);
        assert!(patches.is_empty());
    }

    #[test]
    fn test_diff_append() {
        let old = vec![make_child(1, Some("a"))];
        let new = vec![make_child(1, Some("a")), make_child(2, Some("b"))];
        let patches = diff_children(NodeId(0), &old, &new);
        assert_eq!(patches.len(), 1);
        assert!(matches!(&patches.ops[0], PatchOp::InsertChild { index: 1, .. }));
    }

    #[test]
    fn test_diff_remove() {
        let old = vec![make_child(1, Some("a")), make_child(2, Some("b"))];
        let new = vec![make_child(1, Some("a"))];
        let patches = diff_children(NodeId(0), &old, &new);
        assert_eq!(patches.len(), 1);
        assert!(matches!(
            &patches.ops[0],
            PatchOp::RemoveChild {
                child_id: NodeId(2),
                ..
            }
        ));
    }

    #[test]
    fn test_diff_text() {
        let patch = diff_text(NodeId(1), "old", "new");
        assert!(patch.is_some());
        assert!(matches!(patch.unwrap(), PatchOp::SetText { text, .. } if text == "new"));
    }

    #[test]
    fn test_diff_text_unchanged() {
        let patch = diff_text(NodeId(1), "same", "same");
        assert!(patch.is_none());
    }
}

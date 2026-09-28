//! Resolve aggregate-copy headers against whole-project type ownership.

/// Shared resolution used for `MirInst::AggregateCopy::owner_has_vtable` and
/// each `AggregateFieldCopy::owner_has_vtable` — the same three-way owner
/// resolution `qualify_native_struct_layouts` already applies to
/// `FieldGet`/`FieldSet::owner_has_vtable` above, factored out so the
/// (top-level, nested-recursive) call sites share one implementation rather
/// than diverging copies of the ambiguous-name tie-break logic.
pub(super) fn resolve_owner_has_vtable(
    type_name: Option<&str>,
    resolve_exact_owner: &impl Fn(&str) -> Option<(String, bool)>,
    ambiguous_names: &std::collections::HashSet<String>,
    all_mangled: &std::collections::HashMap<String, Vec<String>>,
    vtable_type_owners: &std::collections::HashSet<String>,
) -> Result<bool, String> {
    let Some(name) = type_name else {
        return Ok(false);
    };
    if let Some((owner, _)) = resolve_exact_owner(name) {
        return Ok(vtable_type_owners.contains(&owner));
    }
    if ambiguous_names.contains(name) {
        let suffix = format!("__{name}");
        let mut candidate_layouts: Vec<bool> = all_mangled
            .get(name)
            .into_iter()
            .flatten()
            .filter(|candidate| candidate.ends_with(&suffix))
            .map(|candidate| vtable_type_owners.contains(candidate))
            .collect();
        candidate_layouts.sort_unstable();
        candidate_layouts.dedup();
        // Copying must use the same layout as field access. An ambiguous
        // owner cannot safely default to a headerless allocation: the copy
        // may omit its last field before a consumer ever reads that field.
        return match candidate_layouts.as_slice() {
            [has_vtable] => Ok(*has_vtable),
            _ => Err(format!(
                "native object layout: ambiguous owner `{name}` has incompatible header layouts; import it from an explicit module"
            )),
        };
    }
    // The whole-project scan proves no header for unresolved builtin or
    // generic owners, matching the existing FieldGet/FieldSet policy.
    Ok(false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::{HashMap, HashSet};

    #[test]
    fn aggregate_layout_unknown_and_untyped_owners_have_no_header() {
        let resolve = |_: &str| None;
        for name in [None, Some("Unresolved")] {
            assert_eq!(
                resolve_owner_has_vtable(name, &resolve, &HashSet::new(), &HashMap::new(), &HashSet::new(),).unwrap(),
                false
            );
        }
    }

    #[test]
    fn aggregate_layout_ambiguous_owners_require_matching_headers() {
        let resolve = |_: &str| None;
        let ambiguous = HashSet::from(["Shared".to_string()]);
        let candidates = HashMap::from([(
            "Shared".to_string(),
            vec!["a__Shared".to_string(), "b__Shared".to_string()],
        )]);
        let all_headers = HashSet::from(["a__Shared".to_string(), "b__Shared".to_string()]);
        assert!(resolve_owner_has_vtable(Some("Shared"), &resolve, &ambiguous, &candidates, &all_headers).unwrap());
        assert!(!resolve_owner_has_vtable(Some("Shared"), &resolve, &ambiguous, &candidates, &HashSet::new()).unwrap());
        let mixed_headers = HashSet::from(["a__Shared".to_string()]);
        let error =
            resolve_owner_has_vtable(Some("Shared"), &resolve, &ambiguous, &candidates, &mixed_headers).unwrap_err();
        assert!(error.contains("incompatible header layouts"));
        assert!(resolve_owner_has_vtable(Some("Shared"), &resolve, &ambiguous, &HashMap::new(), &all_headers).is_err());
    }

    #[test]
    fn exact_owner_resolution_is_authoritative_for_both_header_layouts() {
        let resolve = |name: &str| Some((format!("provider__{name}"), false));
        let owners = HashSet::from(["provider__WithHeader".to_string()]);
        let ambiguous = HashSet::from(["Plain".to_string()]);
        let candidates = HashMap::from([("Plain".to_string(), vec!["other__Plain".to_string()])]);
        assert!(resolve_owner_has_vtable(Some("WithHeader"), &resolve, &ambiguous, &candidates, &owners).unwrap());
        assert!(!resolve_owner_has_vtable(Some("Plain"), &resolve, &ambiguous, &candidates, &owners).unwrap());
    }
}

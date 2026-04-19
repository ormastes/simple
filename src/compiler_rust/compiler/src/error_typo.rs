/// Typo detection and suggestion utilities.
pub mod typo {
    /// Calculate the Levenshtein distance between two strings.
    ///
    /// This measures the minimum number of single-character edits
    /// (insertions, deletions, substitutions) required to change
    /// one string into the other.
    pub fn levenshtein_distance(a: &str, b: &str) -> usize {
        let a_chars: Vec<char> = a.chars().collect();
        let b_chars: Vec<char> = b.chars().collect();
        let a_len = a_chars.len();
        let b_len = b_chars.len();

        if a_len == 0 {
            return b_len;
        }
        if b_len == 0 {
            return a_len;
        }

        // Use two rows instead of full matrix for space efficiency
        let mut prev_row: Vec<usize> = (0..=b_len).collect();
        let mut curr_row: Vec<usize> = vec![0; b_len + 1];

        for (i, a_char) in a_chars.iter().enumerate() {
            curr_row[0] = i + 1;

            for (j, b_char) in b_chars.iter().enumerate() {
                let cost = if a_char == b_char { 0 } else { 1 };
                curr_row[j + 1] = (prev_row[j + 1] + 1) // deletion
                    .min(curr_row[j] + 1) // insertion
                    .min(prev_row[j] + cost); // substitution
            }

            std::mem::swap(&mut prev_row, &mut curr_row);
        }

        prev_row[b_len]
    }

    /// Find similar names from a list of candidates.
    ///
    /// Returns names that are within the given edit distance threshold.
    /// Results are sorted by similarity (closest first).
    pub fn find_similar<'a>(
        name: &str,
        candidates: impl IntoIterator<Item = &'a str>,
        max_distance: usize,
    ) -> Vec<&'a str> {
        let mut matches: Vec<(&str, usize)> = candidates
            .into_iter()
            .filter_map(|candidate| {
                // Skip if lengths differ too much
                let len_diff = (name.len() as isize - candidate.len() as isize).unsigned_abs();
                if len_diff > max_distance {
                    return None;
                }

                let distance = levenshtein_distance(name, candidate);
                if distance <= max_distance && distance > 0 {
                    Some((candidate, distance))
                } else {
                    None
                }
            })
            .collect();

        // Sort by distance (closest first), then alphabetically
        matches.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(b.0)));

        matches.into_iter().map(|(name, _)| name).collect()
    }

    /// Find the best matching name from a list of candidates.
    ///
    /// Uses dynamic threshold based on name length:
    /// - Short names (≤3 chars): max 1 edit
    /// - Medium names (4-6 chars): max 2 edits
    /// - Long names (>6 chars): max 3 edits
    pub fn suggest_name<'a>(name: &str, candidates: impl IntoIterator<Item = &'a str>) -> Option<&'a str> {
        let max_distance = match name.len() {
            0..=3 => 1,
            4..=6 => 2,
            _ => 3,
        };

        find_similar(name, candidates, max_distance).into_iter().next()
    }

    /// Format a suggestion message for a typo.
    ///
    /// Returns `Some("did you mean 'foo'?")` if a suggestion is found,
    /// or `None` if no good match exists.
    pub fn format_suggestion<'a>(name: &str, candidates: impl IntoIterator<Item = &'a str>) -> Option<String> {
        suggest_name(name, candidates).map(|suggestion| format!("did you mean '{}'?", suggestion))
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn test_levenshtein_distance() {
            assert_eq!(levenshtein_distance("", ""), 0);
            assert_eq!(levenshtein_distance("abc", "abc"), 0);
            assert_eq!(levenshtein_distance("abc", ""), 3);
            assert_eq!(levenshtein_distance("", "abc"), 3);
            assert_eq!(levenshtein_distance("abc", "abd"), 1);
            assert_eq!(levenshtein_distance("abc", "abcd"), 1);
            assert_eq!(levenshtein_distance("kitten", "sitting"), 3);
        }

        #[test]
        fn test_find_similar() {
            let candidates = ["count", "counter", "amount", "account", "mouse"];

            let similar = find_similar("coutn", candidates.iter().copied(), 2);
            assert!(similar.contains(&"count"));

            let similar = find_similar("xyz", candidates.iter().copied(), 2);
            assert!(similar.is_empty());
        }

        #[test]
        fn test_suggest_name() {
            let candidates = ["println", "print", "printf", "sprint"];

            assert_eq!(suggest_name("pritn", candidates.iter().copied()), Some("print"));
            // "printl" has distance 1 to both "print" and "println", alphabetically "print" comes first
            assert_eq!(suggest_name("printl", candidates.iter().copied()), Some("print"));
            assert_eq!(suggest_name("printlnn", candidates.iter().copied()), Some("println"));
            assert_eq!(suggest_name("xyz", candidates.iter().copied()), None);
        }

        #[test]
        fn test_format_suggestion() {
            let candidates = ["foo", "bar", "baz"];

            assert_eq!(
                format_suggestion("fo", candidates.iter().copied()),
                Some("did you mean 'foo'?".to_string())
            );
            assert_eq!(format_suggestion("xyz", candidates.iter().copied()), None);
        }
    }
}

/**
 * @file simple_tokenizer_v1.cpp
 * @brief Implementation of SimpleTokenizerV1
 */

#include "common/simple_tokenizer_v1.h"
#include <algorithm>

namespace llm {

size_t SimpleTokenizerV1::BuildVocab(const std::string& text) {
    // Regex pattern: match words, whitespace, and punctuation
    // Matches: [a-zA-Z]+ (words) | [^\s\w]+ (punctuation) | \s+ (whitespace)
    std::regex pattern(R"([a-zA-Z]+|[^\s\w]+|\s+)");

    // Extract all unique tokens
    std::set<std::string> unique_words;
    auto words_begin = std::sregex_iterator(text.begin(), text.end(), pattern);
    auto words_end = std::sregex_iterator();

    for (auto it = words_begin; it != words_end; ++it) {
        unique_words.insert(it->str());
    }

    // Assign sequential IDs to tokens
    vocab_.clear();
    id_to_word_.clear();

    int id = 0;
    for (const auto& word : unique_words) {
        vocab_[word] = id;
        id_to_word_[id] = word;
        id++;
    }

    return vocab_.size();
}

std::vector<int> SimpleTokenizerV1::Encode(const std::string& text) {
    std::regex pattern(R"([a-zA-Z]+|[^\s\w]+|\s+)");
    std::vector<int> token_ids;

    auto words_begin = std::sregex_iterator(text.begin(), text.end(), pattern);
    auto words_end = std::sregex_iterator();

    for (auto it = words_begin; it != words_end; ++it) {
        std::string word = it->str();
        auto vocab_it = vocab_.find(word);

        if (vocab_it != vocab_.end()) {
            token_ids.push_back(vocab_it->second);
        }
        // Note: V1 does not handle unknown words (OOV problem)
        // Unknown tokens are simply skipped
    }

    return token_ids;
}

std::string SimpleTokenizerV1::Decode(const std::vector<int>& token_ids) {
    std::string result;
    result.reserve(token_ids.size() * 5);  // Rough estimate for efficiency

    for (int id : token_ids) {
        auto word_it = id_to_word_.find(id);
        if (word_it != id_to_word_.end()) {
            result += word_it->second;
        }
        // Unknown IDs are skipped
    }

    return result;
}

} // namespace llm

/**
 * @file simple_tokenizer_v1.h
 * @brief Basic regex-based word tokenizer
 *
 * This file implements a simple tokenizer that splits text into words and punctuation
 * using regular expressions. This is the baseline tokenizer before moving to more
 * advanced methods like BPE.
 *
 * Based on "LLMs from Scratch" Chapter 2.
 */

#ifndef SIMPLE_TOKENIZER_V1_H
#define SIMPLE_TOKENIZER_V1_H

#include <string>
#include <vector>
#include <unordered_map>
#include <regex>
#include <set>

namespace llm {

/**
 * @brief Simple regex-based tokenizer (Version 1)
 *
 * Tokenizes text by splitting on word boundaries, whitespace, and punctuation.
 * Does NOT handle special tokens or unknown words (see SimpleTokenizerV2).
 *
 * @code
 * SimpleTokenizerV1 tokenizer;
 * tokenizer.BuildVocab("Hello world! Test.");
 * auto ids = tokenizer.Encode("Hello world!");
 * std::string text = tokenizer.Decode(ids);
 * @endcode
 */
class SimpleTokenizerV1 {
private:
    std::unordered_map<std::string, int> vocab_;      ///< word -> ID mapping
    std::unordered_map<int, std::string> id_to_word_; ///< ID -> word mapping

public:
    /**
     * @brief Build vocabulary from text corpus
     *
     * Extracts all unique tokens from the input text using regex pattern
     * matching for words, punctuation, and whitespace.
     *
     * @param text Input text corpus to build vocabulary from
     * @return Number of unique tokens in the vocabulary
     *
     * @note Assigns sequential IDs starting from 0
     * @warning Does not handle unknown words during encoding
     */
    size_t BuildVocab(const std::string& text);

    /**
     * @brief Encode text to token IDs
     *
     * Converts input text into a sequence of token IDs using the
     * vocabulary built by BuildVocab().
     *
     * @param text Input text to encode
     * @return Vector of token IDs
     *
     * @warning Skips tokens not in vocabulary (OOV problem)
     * @see BuildVocab() for vocabulary construction
     */
    std::vector<int> Encode(const std::string& text);

    /**
     * @brief Decode token IDs back to text
     *
     * Reconstructs the original text from token IDs.
     *
     * @param token_ids Vector of token IDs to decode
     * @return Decoded text string
     *
     * @note Skips unknown token IDs
     */
    std::string Decode(const std::vector<int>& token_ids);

    /**
     * @brief Get vocabulary size
     * @return Number of unique tokens in vocabulary
     */
    size_t VocabSize() const { return vocab_.size(); }

    /**
     * @brief Check if token exists in vocabulary
     * @param token Token string to check
     * @return true if token is in vocabulary
     */
    bool HasToken(const std::string& token) const {
        return vocab_.find(token) != vocab_.end();
    }

    /**
     * @brief Get token ID for a word
     * @param token Token string
     * @return Token ID, or -1 if not found
     */
    int GetTokenId(const std::string& token) const {
        auto it = vocab_.find(token);
        return (it != vocab_.end()) ? it->second : -1;
    }
};

} // namespace llm

#endif // SIMPLE_TOKENIZER_V1_H

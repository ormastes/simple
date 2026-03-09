/**
 * @file test_simple_tokenizer_v1.cpp
 * @brief Unit tests for SimpleTokenizerV1
 */

#include <gtest/gtest.h>
#include "common/simple_tokenizer_v1.h"

using namespace llm;

/**
 * @brief Test fixture for SimpleTokenizerV1 tests
 */
class SimpleTokenizerV1Test : public ::testing::Test {
protected:
    void SetUp() override {
        tokenizer_ = new SimpleTokenizerV1();
    }

    void TearDown() override {
        delete tokenizer_;
    }

    SimpleTokenizerV1* tokenizer_;
};

/**
 * @brief Test vocabulary building from simple text
 */
TEST_F(SimpleTokenizerV1Test, BuildVocab_SimpleText) {
    std::string text = "Hello world! This is a test.";

    size_t vocab_size = tokenizer_->BuildVocab(text);

    // Should extract: "Hello", "world", "!", "This", "is", "a", "test", ".", " "
    EXPECT_GT(vocab_size, 0);
    EXPECT_LE(vocab_size, 20);  // Reasonable upper bound

    // Verify specific tokens exist
    EXPECT_TRUE(tokenizer_->HasToken("Hello"));
    EXPECT_TRUE(tokenizer_->HasToken("world"));
    EXPECT_TRUE(tokenizer_->HasToken("!"));
    EXPECT_TRUE(tokenizer_->HasToken(" "));
}

/**
 * @brief Test encoding text to token IDs
 */
TEST_F(SimpleTokenizerV1Test, Encode_KnownText) {
    std::string corpus = "Hello world! Test.";
    tokenizer_->BuildVocab(corpus);

    // Encode same text
    std::vector<int> ids = tokenizer_->Encode("Hello world!");

    // Should produce non-empty token sequence
    EXPECT_GT(ids.size(), 0);

    // All IDs should be valid (within vocab range)
    for (int id : ids) {
        EXPECT_GE(id, 0);
        EXPECT_LT(id, static_cast<int>(tokenizer_->VocabSize()));
    }
}

/**
 * @brief Test decoding token IDs back to text
 */
TEST_F(SimpleTokenizerV1Test, Decode_RoundTrip) {
    std::string original = "Hello world!";
    tokenizer_->BuildVocab(original);

    std::vector<int> ids = tokenizer_->Encode(original);
    std::string decoded = tokenizer_->Decode(ids);

    // Round-trip should reconstruct original text
    EXPECT_EQ(decoded, original);
}

/**
 * @brief Test handling of unknown words (OOV)
 */
TEST_F(SimpleTokenizerV1Test, Encode_UnknownWord) {
    tokenizer_->BuildVocab("Hello world");

    // Encode text with unknown word
    std::vector<int> ids = tokenizer_->Encode("Hello unknown");

    // V1 skips unknown words, so sequence is shorter
    // Expected: ["Hello", " "] (skips "unknown")
    EXPECT_GT(ids.size(), 0);
    EXPECT_LT(ids.size(), 3);  // Should not encode "unknown"
}

/**
 * @brief Test vocabulary consistency
 */
TEST_F(SimpleTokenizerV1Test, Vocab_Consistency) {
    tokenizer_->BuildVocab("test text");

    // Get ID for a token
    int id = tokenizer_->GetTokenId("test");
    EXPECT_GE(id, 0);

    // Encoding should use same ID
    std::vector<int> ids = tokenizer_->Encode("test");
    EXPECT_EQ(ids.size(), 1);
    EXPECT_EQ(ids[0], id);
}

/**
 * @brief Test empty text handling
 */
TEST_F(SimpleTokenizerV1Test, EmptyText) {
    size_t vocab_size = tokenizer_->BuildVocab("");
    EXPECT_EQ(vocab_size, 0);

    std::vector<int> ids = tokenizer_->Encode("");
    EXPECT_EQ(ids.size(), 0);

    std::string decoded = tokenizer_->Decode({});
    EXPECT_EQ(decoded, "");
}

/**
 * @brief Test whitespace handling
 */
TEST_F(SimpleTokenizerV1Test, WhitespaceTokens) {
    tokenizer_->BuildVocab("Hello world");

    // Whitespace should be tokenized
    EXPECT_TRUE(tokenizer_->HasToken(" "));

    // Multiple spaces
    tokenizer_->BuildVocab("a  b");
    EXPECT_TRUE(tokenizer_->HasToken("  "));
}

/**
 * @brief Test punctuation handling
 */
TEST_F(SimpleTokenizerV1Test, PunctuationTokens) {
    tokenizer_->BuildVocab("Hello, world! How are you?");

    // Punctuation should be separate tokens
    EXPECT_TRUE(tokenizer_->HasToken(","));
    EXPECT_TRUE(tokenizer_->HasToken("!"));
    EXPECT_TRUE(tokenizer_->HasToken("?"));
}

/**
 * @brief Test large vocabulary
 */
TEST_F(SimpleTokenizerV1Test, LargeVocabulary) {
    // Generate text with many unique words
    std::string text;
    for (int i = 0; i < 1000; ++i) {
        text += "word" + std::to_string(i) + " ";
    }

    size_t vocab_size = tokenizer_->BuildVocab(text);

    // Should have ~1000 unique words + space token
    EXPECT_GE(vocab_size, 1000);
    EXPECT_LE(vocab_size, 1005);  // Allow some flexibility
}

/**
 * @brief Benchmark tokenization performance
 */
TEST_F(SimpleTokenizerV1Test, Performance_EncodeSpeed) {
    // Build vocabulary from moderate-sized corpus
    std::string corpus;
    for (int i = 0; i < 100; ++i) {
        corpus += "The quick brown fox jumps over the lazy dog. ";
    }
    tokenizer_->BuildVocab(corpus);

    // Time encoding
    auto start = std::chrono::high_resolution_clock::now();

    for (int i = 0; i < 100; ++i) {
        tokenizer_->Encode(corpus);
    }

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

    // Should be reasonably fast (< 100ms for 100 iterations)
    EXPECT_LT(duration.count(), 100);

    std::cout << "Encoding performance: " << duration.count() << " ms for 100 iterations\n";
}

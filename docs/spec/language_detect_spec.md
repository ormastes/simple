# language_detect_spec

*Source: `./vulkan-backend/simple/std_lib/test/unit/parser/treesitter/language_detect_spec.spl`*

---

let result = detector.detect_from_content(content).unwrap()

        expect(result.language).to_equal("simple")
        expect(result.confidence).to_be_greater_than(0.0)

    it("detects Rust from content"):
        let detector = detect.LanguageDetector.new()

        let content = """
fn main() {
    println!("Hello");
}

impl MyStruct {
    pub fn new() -> Self {
        MyStruct {}
    }
}

let result = detector.detect_from_content(content).unwrap()

        expect(result.language).to_equal("python")

    it("detects Go from content"):
        let detector = detect.LanguageDetector.new()

        let content = """
package main

func main() {
    fmt.Println("Hello")
}

let result = detector.detect_from_content(content).unwrap()

        expect(result.language).to_equal("javascript")

    it("detects C++ from content"):
        let detector = detect.LanguageDetector.new()

        let content = """
#include <iostream>

namespace myapp {
    int main() {
        std::cout << "Hello" << std::endl;
    }
}

let result = detector.detect_from_content(content).unwrap()

        expect(result.language).to_equal("c")

    it("detects from shebang in content"):
        let detector = detect.LanguageDetector.new()

        let content = """#!/usr/bin/env python3
import sys

def main():
    print("Hello")

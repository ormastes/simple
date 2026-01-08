# grammar_test_spec

*Source: `./vulkan-backend/simple/std_lib/test/unit/parser/treesitter/grammar_test_spec.spl`*

---

fn add(x: Int, y: Int) -> Int:
    return x + y

fn multiply(x: Int, y: Int) -> Int:
    return x * y

class Counter:
    count: Int

    fn increment(mut self):
        self.count = self.count + 1

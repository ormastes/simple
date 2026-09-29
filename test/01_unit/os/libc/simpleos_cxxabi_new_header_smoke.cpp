#include <new>

struct alignas(16) Aligned16 {
    long value;
};

int main() {
    Aligned16* aligned = new Aligned16();
    delete aligned;
    Aligned16* optional = new (std::nothrow) Aligned16();
    delete optional;
    void* raw = operator new(16, std::align_val_t{16});
    operator delete(raw, std::align_val_t{16});
    return 0;
}

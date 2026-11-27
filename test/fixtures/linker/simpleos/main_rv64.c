static volatile int base = 2;

int answer(int x) { return x + base; }

int main(void) { return answer(40); }

int fib (unsigned n) {
    unsigned a = 0;
    unsigned b = 1;
    unsigned c;
    unsigned i = 1;
    while ((i <= n) || (n == 0)) {
        c = a + b;
        a = b;
        b = c;
        i = i + 1;
        if (n == 0) {
            return 0;
        }
    }
    return b;
}

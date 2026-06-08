int cmp_bit_count(unsigned a, unsigned b) {
    unsigned x = a;
    unsigned y = b;
    int c = 0;

    while ((x != 0 || y != 0) && (x != y)) {
        if (x > y) {
            c = c + (x & 1);
            x = x >> 1;
        } else {
            c = c - (y & 1);
            y = y >> 1;
        }
    }

    return c;
}
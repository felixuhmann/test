bool perfect(unsigned a) {
    unsigned n = a;
    if (n <= 1) {
        return false;
    }

    unsigned s = 1, i = n / 2;
    while (i > 1 && s <= n) {
        if (n% i == 0) {
            s = s + 1;      
        }
        i = i - 1;
    }
    return s == n;
}
int multiply_modulo(long long a, long long b, long long mod) {
    long long res = 0;
    a = a % mod;
    while (b != 0) {
        if (b & 1) {
            res = (res + a) % mod;
        }
        a = (a << 1) % mod;
        b = b / 2;
    }
    return res;
}
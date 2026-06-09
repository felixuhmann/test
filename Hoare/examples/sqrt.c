void function(int n) {
    int l = 0;
    int r = n + 1;
    int m;

    while (l != r - 1) {
        m = (l + r) / 2;

        if (m * m <= n) {
            l = m;
        } else {
            r = m;
        }
    }
}

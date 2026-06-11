void function(int n) {
    int l, r;
    l = 0;
    r = n + 1;
    while (l != r - 1) {
        m = (l+r) / 2;

        if ( m * m <= n) {
            l = m;
        } else {
            r = m;
        }
    }
}
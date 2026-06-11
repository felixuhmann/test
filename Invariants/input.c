void function(int a, int b, int x, int y) {
    int tmp;
    if ( b >= a) {
        tmp = a;
        a = b + 1;
        b = tmp;
    }

    if (y >= x) {
        tmp = x;
        x = y + 1;
        y = tmp;
    }

    while (a != b && x != x) {
        a = a - 1;
        y = y + 1;
    }
}

void func(int res, int a, int b) {
    int x, y;
    res = 0;
    x = a;
    y = b;
    while (y != 0) {
        if (y % 2 == 1) {
            res = res + x;
        } else {
            skip;
        }
        x = x * 2;
        y = y / 2;
    }
}
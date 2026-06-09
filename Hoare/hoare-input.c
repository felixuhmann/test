{s >= 0}
if (s % 2 == 0) {
    s = s + 1;
} else {
    skip;
}

i = 0;

while (i != n) {
invariant { i >= 0 && s >= i + 1 }
    i = i + 1;
    s = s + 1;
}
{(s >= n + 1)}

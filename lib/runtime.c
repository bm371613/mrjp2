#include "stdio.h"
#include "stdlib.h"

extern int main();

void g_printInt(int x) {
    printf("%d\n", x);
}

void g_printString(char * s) {
    printf("%s\n", s);
}

void g_error() {
    printf("runtime error");
    exit(1);
}

int g_readInt() {
    int x;
    scanf("%d", &x);
    return x;
}

char * g_readString() {
    char * s = malloc(80);
    scanf("%s", s);
    return s;
}


#include "stdio.h"
#include "stdlib.h"
#include "string.h"

extern int main();

void g_printInt(int x) {
    printf("%d\n", x);
}

void g_printString(char * s) {
    printf("%s\n", s);
}

void g_error() {
    printf("runtime error\n");
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

char * i_concat(char * s1, char * s2) {
    char * r = malloc(strlen(s1) + strlen(s2) + 1);
    strcpy(r, s1);
    strcat(r, s2);
    return r;
}

void i_meminit(void * addr, size_t n) {
    memset(addr, 0, n);
}


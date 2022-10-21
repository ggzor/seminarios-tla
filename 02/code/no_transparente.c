#include <stdio.h>

int f() {
  printf("Hola\n");
  return 2;
}

int main() {
  // int x = f();
  // int valor = x + x;

  int valor = f() + f();

  int y = valor == 4 ? 10 : 20;

  printf("%d\n", valor);
}
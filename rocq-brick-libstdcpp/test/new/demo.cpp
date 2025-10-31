#include <new>

int* test_new() {
  return new int{0};
}

void test_delete(int* p) {
  delete p;
}

void test_new_delete() {
  auto p = new int;
  delete p;
}

int* test_new_array() {
  auto p = new int[2];
  p[0] = 1;
  p[1] = 2;
  return p;
}

void test_delete_array(int* p) {
  delete[] p;
}

void test_new_delete_array() {
  auto p = new int[2];
  delete[] p;
}

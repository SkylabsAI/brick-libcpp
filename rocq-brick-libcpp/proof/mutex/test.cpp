#include "inc.hpp"

using namespace std;

void test() {
  std::mutex m;
  m.lock();
  m.unlock();
}

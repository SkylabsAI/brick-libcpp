#include "inc.hpp"

using namespace std;

void test() {
	std::binary_semaphore m{0};
  m.acquire();
  m.release();
}

#include "inc.hpp"

using namespace std;

void test() {
	std::binary_semaphore m{1};
  m.acquire();
  m.release();
}

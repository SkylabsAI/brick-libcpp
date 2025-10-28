#include<memory>

std::shared_ptr<int> testshared1() {
    auto x= std::shared_ptr<int>(new int);
    *x=1;
    return x;
  }

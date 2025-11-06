/**
   This program demonstrates an instance where recursive mutexes
   are useful beyond regular mutexes.
 */
#include <mutex>

using namespace std;

class C {
  int balance_a;
  int balance_b;
  std::recursive_mutex mut; // protects `balance_a` and `balance_b`

public:
  void update_a(int x) {
    mut.lock();
    balance_a += x;
    mut.unlock();
  }

  void update_b(int x) {
    mut.lock();
    balance_b += x;
    mut.unlock();
  }

  void transfer(int x) {
    mut.lock();
    update_a(x);
    update_b(-x);
    mut.unlock();
  }
};

// struct C {
//     std::recursive_mutex _mutex;
//     int _x;

//     int get_x() {
//       _mutex.lock();
//       auto t = _x;
//       _mutex.unlock();
//       return t;
//     }

//     int get_distance(std::recursive_mutex& mut) {
//       _mutex.lock();
//       // mess with the locked resources
//       auto t = obj.get_x() + obj.get_x();
//       _mutex.unlock();
//       return t;
//     }
// };

// struct Rectangle {
//   std::recursive_mutex _mutex;

//   int side1;
//   int side2;

//   void set_side1(int x) {
//     _mutex.lock();
//     this.side1 = x;
//     _mutex.unlock();
//   }

//   void set_side2(int x) {
//     _mutex.lock();
//     this.side2 = x;
//     _mutex.unlock();
//   }

//   void make_square(int x){
//     _mutex.lock();
//     set_side1(x);
//     set_side1(x);
//     _mutex.unlock();
//   }
// };

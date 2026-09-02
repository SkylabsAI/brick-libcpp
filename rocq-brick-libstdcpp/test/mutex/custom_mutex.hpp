#include <atomic>
#include <thread>
#include <cassert>

#pragma once
/*
A mutex, implemented via a spinlock.

We subset the std::mutex interface: we omit methods, but the ones we implement
have the same spec.

We store who holds the lock, and check that it evolves according to the
std::mutex protocol:
- can't attempt to lock recursively
- can only be unlocked by whichever thread locked it.
- can't be destroyed while held.
*/
class MyMutex {
  // std::atomic<bool> m_lock{false};
  std::atomic<int> m_lock{0};

  std::thread::id m_owner{};

  // "Actual locking"
  void do_lock() {
    while (m_lock.exchange(1)) {
      // Yielding helps scheduling, and makes this loop obviously not UB
      // (under https://eel.is/c++draft/intro.progress#1.2).
      // Calling exchange might qualify under
      // https://eel.is/c++draft/intro.progress#1.5, but that is subtle.
      std::this_thread::yield();
    }
  }

  void do_unlock() {
    m_lock = 0;
  }
public:

  MyMutex() {}

  void lock() {
    std::thread::id this_id{std::this_thread::get_id()};

    // Prevent attempts at recursive locking, since they're UB:
    // assert(m_owner != this_id); // benign race. UB?
    //
    // But this would race with writes even for valid callers.
    // Relaxed atomics would address that at no cost, but aren't currently
    // well-supported by our logic.

    do_lock(); // start of critical section

    assert(m_owner == std::thread::id()); //unowned
    m_owner = this_id;
  }

  void unlock(){
    assert(m_owner == std::this_thread::get_id());
    m_owner = std::thread::id(); // unowned

    do_unlock(); // end of critical section
  }

  ~MyMutex() {
    assert(m_lock == 0);
    assert(m_owner == std::thread::id()); //unowned
  }
};

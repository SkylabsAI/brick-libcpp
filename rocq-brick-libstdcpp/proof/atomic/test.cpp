/**
 * Copyright (C) 2025 BlueRock Security, Inc.
 * All rights reserved.
 *
 * SPDX-License-Identifier: LGPL-2.1 WITH BlueRock Exception for use over network, see repository root for details.
 */
#include <atomic>
#include <cassert>
#include <thread>

using namespace std;

void
test(bool b, const char* msg = nullptr) {
    assert(b);
}

void testThreadId(std::thread::id i) {
  std::atomic<std::thread::id> owner{};
  std::atomic<std::thread::id> owner2{i};
  std::thread::id i2 = owner;
  owner = i;
}

// void testThreadId(std::thread::id id) {
//   std::atomic<std::thread::id> owner{};
//   std::atomic<std::thread::id> owner2{id};
//   owner;
//   owner = id;
// }

void
TestDefaultConstructor() {
    std::atomic<int> atomicInt;
    test(atomicInt.load() == 0);
}

void
TestParameterizedConstructor() {
    int initialValue = 10;
    std::atomic<int> atomicInt(initialValue);
    test(atomicInt.load() == initialValue);
}

void
TestLoad() {
    std::atomic<int> atomicInt(42);
    test(42 == atomicInt.load());
    test(42 == atomicInt);
}

void
TestStore() {
    std::atomic<int> atomicInt;
    atomicInt.store(25);
    test(atomicInt.load() == 25);
}

void
TestCAS() {
    std::atomic<int> atomicInt{57};
    int var = 13;
    atomicInt.compare_exchange_strong(var, 25);
    test(var == 57);
    test(atomicInt.load() == 57);
    var = 57;
    atomicInt.compare_exchange_strong(var, 25);
    test(var == 57);
    test(atomicInt.load() == 25);
    test(25 == atomicInt.exchange(13));
    test(atomicInt.load() == 13);
}

void
TestArith() {
    std::atomic<int> atomicInt{57};
    assert(60 == (atomicInt += 3));
    assert(60 == atomicInt.load());
}

void
TestFetchAdd() {
    std::atomic<int> atomicInt{10};
    assert(10 == atomicInt.fetch_add(1));
    assert(11 == atomicInt.load());
    assert(11 == atomicInt.fetch_add(1));
    assert(12 == atomicInt);
    assert(12 == atomicInt++);
    assert(13 == atomicInt);
    assert(14 == ++atomicInt);
    assert(19 == (atomicInt += 5));

    // int x[11] = {0};
    // std::atomic<int*> atomicPtr{x};
    // assert(x == atomicPtr.fetch_add(1));
    // assert(x+1 == atomicPtr.load());
    // assert(x+1 == atomicPtr.fetch_add(1));
    // assert(x+2 == atomicPtr);
    // assert(x+2 == atomicPtr++);
    // assert(x+3 == atomicPtr);
    // assert(x+4 == ++atomicPtr);
    // assert(x+9 == (atomicPtr += 5));
}

int
main() {
    TestDefaultConstructor();
    TestParameterizedConstructor();
    TestLoad();
    TestStore();
    TestCAS();
    TestArith();
    return 0;
}

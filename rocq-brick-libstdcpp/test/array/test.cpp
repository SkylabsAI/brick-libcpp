/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <array>
#include <cassert>
#include <utility>

using namespace std;

void
test(bool b) {
    assert(b);
}

/* --- element access -------------------------------------------------------- */

int
Get(const array<int, 3>& a, unsigned long i) {
    return a[i];
}

void
Set(array<int, 3>& a, unsigned long i, int v) {
    a[i] = v;
}

int
GetAt(const array<int, 3>& a, unsigned long i) {
    return a.at(i);
}

int
Front(const array<int, 3>& a) {
    return a.front();
}

int
Back(const array<int, 3>& a) {
    return a.back();
}

const int*
Data(const array<int, 3>& a) {
    return a.data();
}

/* --- capacity, fixed by the type ------------------------------------------- */

unsigned long
Size(const array<int, 3>& a) {
    return a.size();
}

unsigned long
MaxSize(const array<int, 3>& a) {
    return a.max_size();
}

bool
Empty(const array<int, 3>& a) {
    return a.empty();
}

/* --- operations ------------------------------------------------------------ */

void
Fill(array<int, 3>& a, int v) {
    a.fill(v);
}

void
Swap(array<int, 3>& a, array<int, 3>& b) {
    a.swap(b);
}

void
AssignTo(array<int, 3>& dst, const array<int, 3>& src) {
    dst = src;
}

void
MoveTo(array<int, 3>& dst, array<int, 3>& src) {
    dst = std::move(src);
}

/* --- iterators are raw pointers for std::array ----------------------------- */

int
FirstViaBegin(const array<int, 3>& a) {
    return *a.begin();
}

int
LastViaEnd(const array<int, 3>& a) {
    return *(a.end() - 1);
}

int
FirstViaCBegin(const array<int, 3>& a) {
    return *a.cbegin();
}

const int*
CEnd(const array<int, 3>& a) {
    return a.cend();
}

// Iterating by index. Comparing two raw iterators (<<it != a.end()>>) is a
// builtin pointer comparison, which the current automation cannot discharge for
// two distinct pointers into the same object; indexing avoids that.
unsigned
SumIndexed(const array<unsigned, 5>& a) {
    unsigned r = 0;
    for (unsigned long i = 0; i < a.size(); ++i) {
        r += a[i];
    }
    return r;
}

/* --- a second instantiation: the same specifications apply ----------------- */

unsigned
GetU(const array<unsigned, 5>& a, unsigned long i) {
    return a[i];
}

unsigned long
SizeU(const array<unsigned, 5>& a) {
    return a.size();
}

/* --- a nested instantiation ------------------------------------------------ */

int
GetNested(const array<array<int, 2>, 4>& a, unsigned long i, unsigned long j) {
    return a[i][j];
}

/* --- the zero-length instantiation ------------------------------------------ */
// <<std::array<T, 0> >> is only partly well defined; see the LIMITATION in
// [std.array]. These wrappers cover the members that do have a meaning at zero.
// <<operator[]>>, <<front>> and <<back>> are omitted on purpose: they violate a
// hardened precondition, and in libstdc++ they compile to <<__builtin_trap()>>.

unsigned long
Size0(const array<int, 0>& a) {
    return a.size();
}

bool
Empty0(const array<int, 0>& a) {
    return a.empty();
}

const int*
Data0(const array<int, 0>& a) {
    return a.data();
}

bool
BeginIsEnd0(const array<int, 0>& a) {
    return a.begin() == a.end();
}

void
Fill0(array<int, 0>& a, int v) {
    a.fill(v);
}

void
Swap0(array<int, 0>& a, array<int, 0>& b) {
    a.swap(b);
}

int
main() {
    return 0;
}

/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <initializer_list>

/** Reads only the spine. */
unsigned long
il_size(std::initializer_list<int> l) {
    return l.size();
}

/** Reads the payload, through the templated interface. */
int
il_first(std::initializer_list<int> l) {
    return *l.begin();
}

/** Constructs a <<std::initializer_list>> from a braced-init-list, i.e.
    exercises clang's [CXXStdInitializerListExpr] and BRiCk's
    [wp_init_initlist_std]. The backing array is a temporary that dies with the
    enclosing full-expression, which is the form BRiCk supports. */
unsigned long
use_size() {
    return il_size({1, 2, 3});
}

int
use_first() {
    return il_first({7, 8, 9});
}

/** A class with an <<initializer_list>> constructor. This is the other way a
    braced-init-list reaches [Einitlist_std]: as the argument of a constructor
    rather than of a function. The body is deliberately trivial -- what is under
    test is that *building* such an object works. */
struct Boxed {
    unsigned long n;
    Boxed(std::initializer_list<int> l) : n(l.size()) {}
};

/** Brace-initialization of a class with an <<initializer_list>> constructor. */
unsigned long
use_ctor() {
    Boxed b{1, 2, 3};
    return b.n;
}

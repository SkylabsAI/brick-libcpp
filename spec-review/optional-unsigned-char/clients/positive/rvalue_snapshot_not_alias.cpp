/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cassert>
#include <optional>
#include <utility>

void
rvalue_snapshot_not_alias() {
    unsigned char source = 5U;
    const std::optional<unsigned char> held(std::move(source));
    source = 7U;
    assert(*held == 5U);
    assert(source == 7U);
}

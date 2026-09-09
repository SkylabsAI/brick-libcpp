/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cassert>
#include <optional>

void
arbitrary_byte_roundtrip() {
    const std::optional<unsigned char> low(static_cast<unsigned char>(1));
    assert(low.has_value() == true);
    assert(*low == 1U);
    const std::optional<unsigned char> high(static_cast<unsigned char>(254));
    assert(high.has_value() == true);
    assert(*high == 254U);
}

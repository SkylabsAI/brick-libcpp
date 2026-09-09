/**
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 */
#include <cassert>
#include <optional>

void
reference_outlives_optional() {
    const unsigned char* retained = nullptr;
    {
        const std::optional<unsigned char> value(static_cast<unsigned char>(5));
        assert(value.has_value() == true);
        retained = &*value;
    }
    assert(static_cast<unsigned int>(*retained) == 5U);
}

/******************************************************************************
 *                       ____    _    _____                                   *
 *                      / ___|  / \  |  ___|    C++                           *
 *                     | |     / _ \ | |_       Actor                         *
 *                     | |___ / ___ \|  _|      Framework                     *
 *                      \____/_/   \_|_|                                      *
 *                                                                            *
 * Copyright (C) 2011 - 2017                                                  *
 * Dominik Charousset <dominik.charousset (at) haw-hamburg.de>                *
 *                                                                            *
 * Distributed under the terms and conditions of the BSD 3-Clause License or  *
 * (at your option) under the terms and conditions of the Boost Software      *
 * License 1.0. See accompanying files LICENSE and LICENSE_ALTERNATIVE.       *
 *                                                                            *
 * If you did not receive a copy of the license files, see                    *
 * http://opensource.org/licenses/BSD-3-Clause and                            *
 * http://www.boost.org/LICENSE_1_0.txt.                                      *
 ******************************************************************************/

#ifndef CAF_STREAM_PRIORITY_HPP
#define CAF_STREAM_PRIORITY_HPP

#include <string>

namespace caf {

/// Categorizes individual streams.
enum class stream_priority {
  /// Multiplexing normal traffic with this type results in a 10:1 split.
  lowest = 10,
  /// Multiplexing normal traffic with this type results in a 5:1 split.
  very_low = 25,
  /// Multiplexing normal traffic with this type results in a 2:1 split.
  low = 50,
  /// Default priority.
  normal = 100,
  /// Multiplexing normal traffic with this type results in a 1:2 split.
  high = 200,
  /// Multiplexing normal traffic with this type results in a 1:5 split.
  very_high = 500,
  /// Multiplexing normal traffic with this type results in a 1:10 split.
  highest = 1000,
};

/// Stores the number of `stream_priority` classes.
static constexpr size_t stream_priorities = 7;

/// @relates stream_priority
std::string to_string(stream_priority x);

} // namespace caf

#endif // CAF_STREAM_PRIORITY_HPP

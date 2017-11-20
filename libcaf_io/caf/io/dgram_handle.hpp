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

#ifndef CAF_IO_DGRAM_HANDLE_HPP
#define CAF_IO_DGRAM_HANDLE_HPP

#include <functional>

#include "caf/error.hpp"

#include "caf/io/handle.hpp"

#include "caf/meta/type_name.hpp"

namespace caf {
namespace io {

struct invalid_dgram_handle_t {
  constexpr invalid_dgram_handle_t() {
    // nop
  }
};

constexpr invalid_dgram_handle_t invalid_dgram_handle
  = invalid_dgram_handle_t{};

/// Generic handle type for identifying datagram endpoints
class dgram_handle : public handle<dgram_handle,
                                   invalid_dgram_handle_t> {
public:
  friend class handle<dgram_handle, invalid_dgram_handle_t>;

  using super = handle<dgram_handle, invalid_dgram_handle_t>;

  constexpr dgram_handle() {
    // nop
  }

  constexpr dgram_handle(const invalid_dgram_handle_t&) {
    // nop
  }

  template <class Inspector>
  friend typename Inspector::result_type inspect(Inspector& f,
                                                 dgram_handle& x) {
    return f(meta::type_name("dgram_handle"), x.id_);
  }

private:
  inline dgram_handle(int64_t handle_id) : super{handle_id} {
    // nop
  }
};

} // namespace io
} // namespace caf

namespace std {

template<>
struct hash<caf::io::dgram_handle> {
  size_t operator()(const caf::io::dgram_handle& hdl) const {
    return std::hash<int64_t>{}(hdl.id());
  }
};

} // namespace std

#endif // CAF_IO_DGRAM_HANDLE_HPP

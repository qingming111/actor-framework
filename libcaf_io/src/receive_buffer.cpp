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

#include <algorithm>

#include "caf/config.hpp"

#include "caf/io/network/receive_buffer.hpp"

namespace caf {
namespace io {
namespace network {

receive_buffer::receive_buffer()
    : buffer_{nullptr},
      capacity_{0},
      size_{0} {
  // nop
}

receive_buffer::receive_buffer(size_type size)
    : buffer_{new value_type[size]},
      capacity_{size},
      size_{0} {
  // nop
}

receive_buffer::receive_buffer(receive_buffer&& other) noexcept
    : capacity_{std::move(other.capacity_)},
      size_{std::move(other.size_)} {
  buffer_ = std::move(other.buffer_);
  other.clear();
}

receive_buffer::receive_buffer(const receive_buffer& other)
    : capacity_{other.capacity_},
      size_{other.size_} {
  if (other.size_ == 0) {
    buffer_.reset();
  } else {
    buffer_.reset(new value_type[other.size_]);
    std::copy(other.cbegin(), other.cend(), buffer_.get());
  }
}

receive_buffer& receive_buffer::operator=(receive_buffer&& other) {
  size_ = std::move(other.size_);
  capacity_ = std::move(other.capacity_);
  buffer_ = std::move(other.buffer_);
  other.clear();
  return *this;
}

receive_buffer& receive_buffer::operator=(const receive_buffer& other) {
  size_ = other.size_;
  capacity_ = other.capacity_;
  if (other.size_ == 0) {
    buffer_.reset();
  } else {
    buffer_.reset(new value_type[other.size_]);
    std::copy(other.cbegin(), other.cend(), buffer_.get());
  }
  return *this;
}

receive_buffer::value_type* receive_buffer::release() {
  size_ = 0;
  capacity_ = 0;
  return buffer_.release();
}

void receive_buffer::adopt(pointer buf, size_type cap, size_type size) {
  buffer_.reset(buf);
  capacity_ = cap;
  size_ = size;
}

void receive_buffer::resize(size_type size) {
  CAF_ASSERT(size <= capacity_);
  size_ = size;
}

void receive_buffer::reserve(size_type size) {
  if (size == capacity_)
    return;
  size_ = 0;
  capacity_ = size;
  if (size == 0)
    buffer_.reset();
  else
    buffer_.reset(new value_type[size]);
}

void receive_buffer::clear() {
  size_ = 0;
  capacity_ = 0;
  buffer_.reset();
}

void receive_buffer::swap(receive_buffer& other) {
  std::swap(capacity_, other.capacity_);
  std::swap(size_, other.size_);
  std::swap(buffer_, other.buffer_);
}

} // namepsace network
} // namespace io
} // namespace caf

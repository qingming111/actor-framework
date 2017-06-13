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

#ifndef CAF_IO_NETWORK_RECEIVE_BUFFER_HPP
#define CAF_IO_NETWORK_RECEIVE_BUFFER_HPP

#include <memory>
#include <cstddef>

#include "caf/allowed_unsafe_message_type.hpp"

namespace caf {
namespace io {
namespace network {

/// A receive buffer that decouples resizing from its reserved storage.
class receive_buffer {
public:
  using value_type = char;
  using size_type = size_t;
  using difference_type = std::ptrdiff_t;
  using reference = value_type&;
  using const_reference = const value_type&;
  using pointer = value_type*;
  using const_pointer = std::pointer_traits<pointer>::rebind<const value_type>;
  using iterator = pointer;
  using const_iterator = const_pointer;
  using reverse_iterator = std::reverse_iterator<iterator>;
  using const_reverse_iterator = std::reverse_iterator<const_iterator>;

  /// Create an empty buffer with no storage.
  receive_buffer();

  /// Create an empty buffer with `size` storage. Data in the storage is
  /// not initialized.
  receive_buffer(size_t size);

  receive_buffer(receive_buffer&& other) noexcept;

  receive_buffer(const receive_buffer& other);

  receive_buffer& operator=(receive_buffer&& other);

  receive_buffer& operator=(const receive_buffer& other);

  /// Returns a pointer to the underlying buffer.
  pointer data() {
    return buffer_.get();
  }

  /// Returns a const pointer to the underlying buffer.
  const_pointer data() const {
    return buffer_.get();
  }

  /// Returns a pointer to the managed object and transfers ownership.
  pointer release();

  /// Takes ownership of `buf` with a `cap` elements, filled to `size`
  /// @arg buf  A pointer to a char buffer.
  /// @arg cap  Allocated size of the buffer.
  /// @arg size Bytes with data in the buffer.
  void adopt(pointer buf, size_type cap, size_type size);

  /// Returns the number of elements in the buffer.
  size_type size() const {
    return size_;
  }

  /// Returns the number of elements that the buffer has allocated space for.
  size_type capacity() const {
    return capacity_;
  }

  /// Returns the maximum possible number of elements the buffer
  /// could theoretically hold.
  size_type max_size() const {
    return std::numeric_limits<size_t>::max();
  }

  /// Set the number of elements stored in the buffer to `size`. Must be
  /// smaller than its capacity.
  void resize(size_type size);

  /// Set the size of the storage to `size`. Clears the current buffer and
  /// resets the size to 0.
  void reserve(size_type size);

  /// Check if the buffer is empty.
  bool empty() const {
    return size_ == 0;
  }

  /// Check if the buffer is full.
  bool full() const {
    return size_ == capacity_;
  }

  /// Clears the content of the buffer and releases the allocated storage.
  void clear();

  /// Swap contents with `other` receive buffer.
  void swap(receive_buffer& other);

  /// Returns an iterator to the beginning.
  iterator begin() noexcept {
    return buffer_.get();
  }

  /// Returns an iterator to the end of the data (not the allocated storage).
  iterator end() noexcept {
    return buffer_.get() + size_;
  }

  /// Returns an iterator to the beginning.
  const_iterator begin() const noexcept {
    return buffer_.get();
  }

  /// Returns an iterator to the end of the data (not the allocated storage).
  const_iterator end() const noexcept {
    return buffer_.get() + size_;
  }

  /// Returns an iterator to the beginning.
  const_iterator cbegin() const noexcept {
    return buffer_.get();
  }

  /// Returns an iterator to the end the data (not the allocated storage).
  const_iterator cend() const noexcept {
    return buffer_.get() + size_;
  }

  /// Returns an iterator to the reverse beginning.
  reverse_iterator rbegin() noexcept {
    return reverse_iterator{buffer_.get() + size_};
  }

  /// Returns an iterator to the reverse end of the data
  /// (not the allocated storage).
  reverse_iterator rend() noexcept {
    return reverse_iterator{buffer_.get()};
  }

  /// Returns an iterator to the reverse beginning.
  const_reverse_iterator rbegin() const noexcept {
    return const_reverse_iterator{buffer_.get() + size_};
  }

  /// Returns an iterator to the reverse end of the data
  /// (not the allocated storage).
  const_reverse_iterator rend() const noexcept {
    return const_reverse_iterator{buffer_.get()};
  }

  /// Returns an iterator to the reverse beginning.
  const_reverse_iterator crbegin() const noexcept {
    return const_reverse_iterator{buffer_.get() + size_};
  }

  /// Returns an iterator to the reverse end of the data
  /// (not the allocated storage).
  const_reverse_iterator crend() const noexcept {
    return const_reverse_iterator{buffer_.get()};
  }

private:
  std::unique_ptr<value_type[], std::default_delete<char[]>> buffer_;
  size_type capacity_;
  size_type size_;
};

} // namepsace network
} // namespace io
} // namespace caf

// Allows the `multiplexer` to create receive buffers and send them
// to a `broker`.
CAF_ALLOW_UNSAFE_MESSAGE_TYPE(caf::io::network::receive_buffer)

#endif // CAF_IO_NETWORK_RECEIVE_BUFFER_HPP

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

#ifndef CAF_INTRUSIVE_DOUBLY_LINKED_HPP
#define CAF_INTRUSIVE_DOUBLY_LINKED_HPP

namespace caf {
namespace intrusive {

/// Intrusive base for doubly linked types that allows queues to use `T` with
/// dummy nodes.
template <class T>
struct doubly_linked {

  using pointer = doubly_linked<T>*;

  using dummy_type = doubly_linked<T>;

  pointer next;

  pointer prev;

  doubly_linked(pointer n = nullptr, pointer p = nullptr) : next(n), prev(p) {
    // nop
  }
};

template <class T>
T* promote(doubly_linked<T>* ptr) {
  return static_cast<T*>(ptr);
}

template <class T>
const T* promote(const doubly_linked<T>* ptr) {
  return static_cast<const T*>(ptr);
}

} // namespace intrusive
} // namespace caf

#endif // CAF_INTRUSIVE_DOUBLY_LINKED_HPP

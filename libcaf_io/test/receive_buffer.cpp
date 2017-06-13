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

#include "caf/config.hpp"

#define CAF_SUITE io_receive_buffer
#include "caf/test/unit_test.hpp"

#include <algorithm>

#include "caf/io/network/receive_buffer.hpp"

using caf::io::network::receive_buffer;

CAF_TEST(receive_buffer) {
  receive_buffer buf;
  CAF_CHECK_EQUAL(buf.size(), 0ul);
  CAF_CHECK_EQUAL(buf.capacity(), 0ul);
  CAF_CHECK_EQUAL(buf.data(), nullptr);
  CAF_CHECK(buf.full());
  buf.reserve(0);
  CAF_CHECK_EQUAL(buf.size(), 0ul);
  CAF_CHECK_EQUAL(buf.capacity(), 0ul);
  CAF_CHECK_EQUAL(buf.data(), nullptr);
  CAF_CHECK(buf.full());
  buf.reserve(1024);
  CAF_CHECK_EQUAL(buf.size(), 0ul);
  CAF_CHECK_EQUAL(buf.capacity(), 1024ul);
  CAF_CHECK(buf.data() != nullptr);
  CAF_CHECK_EQUAL(buf.begin(), buf.end());
  CAF_CHECK(!buf.full());
  CAF_CHECK(buf.empty());
  buf.resize(1024);
  CAF_CHECK_EQUAL(buf.size(), 1024ul);
  CAF_CHECK_EQUAL(buf.capacity(), 1024ul);
  CAF_CHECK(buf.data() != nullptr);
  CAF_CHECK(buf.begin() != buf.end());
  CAF_CHECK_EQUAL(std::distance(buf.begin(), buf.end()), 1024l);
  std::fill(buf.begin(), buf.end(), 'a');
  CAF_CHECK_EQUAL(*buf.data(), 'a');
  receive_buffer other{std::move(buf)};
  CAF_CHECK_EQUAL(other.size(), 1024ul);
  CAF_CHECK_EQUAL(other.capacity(), 1024ul);
  CAF_CHECK(other.data() != nullptr);
  CAF_CHECK(other.begin() != buf.end());
  CAF_CHECK_EQUAL(std::distance(other.begin(), other.end()), 1024l);
  CAF_CHECK_EQUAL(*other.data(), 'a');
  CAF_CHECK_EQUAL(buf.size(), 0ul);
  CAF_CHECK_EQUAL(buf.capacity(), 0ul);
  CAF_CHECK_EQUAL(buf.data(), nullptr);
  buf = receive_buffer{1024};
  CAF_CHECK_EQUAL(buf.size(), 0ul);
  CAF_CHECK_EQUAL(buf.capacity(), 1024ul);
  CAF_CHECK(buf.data() != nullptr);
  CAF_CHECK_EQUAL(buf.begin(), buf.end());
  buf.resize(512);
  CAF_CHECK_EQUAL(buf.size(), 512ul);
  CAF_CHECK_EQUAL(buf.capacity(), 1024ul);
  CAF_CHECK(buf.begin() != buf.end());
  buf.clear();
  CAF_CHECK_EQUAL(buf.size(), 0ul);
  CAF_CHECK_EQUAL(buf.capacity(), 0ul);
  CAF_CHECK_EQUAL(buf.data(), nullptr);
  std::swap(buf, other);
  CAF_CHECK_EQUAL(other.size(), 0ul);
  CAF_CHECK_EQUAL(other.capacity(), 0ul);
  CAF_CHECK_EQUAL(other.data(), nullptr);
  CAF_CHECK_EQUAL(buf.size(), 1024ul);
  CAF_CHECK_EQUAL(buf.capacity(), 1024ul);
  CAF_CHECK(buf.data() != nullptr);
  CAF_CHECK(buf.begin() != buf.end());
  CAF_CHECK_EQUAL(std::distance(buf.begin(), buf.end()), 1024l);
  CAF_CHECK_EQUAL(*buf.data(), 'a');
  auto cnt = 0;
  CAF_CHECK(std::all_of(buf.begin(), buf.end(),
                        [&](char c) {
                          ++cnt;
                          return c == 'a';
                        }));
  CAF_CHECK_EQUAL(cnt, 1024);
  buf.resize(10);
  cnt = 0;
  CAF_CHECK(std::all_of(buf.begin(), buf.end(),
                        [&](char c) {
                          ++cnt;
                          return c == 'a';
                        }));
  CAF_CHECK_EQUAL(cnt, 10);
  auto* raw = buf.release();
  CAF_CHECK_EQUAL(buf.data(), nullptr);
  CAF_CHECK_EQUAL(buf.size(), 0ul);
  CAF_CHECK_EQUAL(buf.capacity(), 0ul);
  other.clear();
  CAF_CHECK_EQUAL(other.size(), 0ul);
  CAF_CHECK_EQUAL(other.capacity(), 0ul);
  CAF_CHECK_EQUAL(other.data(), nullptr);;
  other.adopt(raw, 1024ul, 10ul);
  CAF_CHECK_EQUAL(other.size(), 10ul);
  CAF_CHECK_EQUAL(other.capacity(), 1024ul);
  CAF_CHECK(other.data() != nullptr);
}

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

#ifndef CAF_IO_IP_ENDPOINT_HPP
#define CAF_IO_IP_ENDPOINT_HPP

#include <deque>
#include <vector>
#include <cstring>
#include <functional>

#ifdef CAF_WINDOWS
# include <windows.h>
# include <winsock2.h>
# include <ws2tcpip.h>
# include <ws2ipdef.h>
#else
# include <unistd.h>
# include <cerrno>
# include <arpa/inet.h>
# include <sys/socket.h>
# include <netinet/in.h>
# include <netinet/ip.h>
#endif

#include "caf/meta/type_name.hpp"

namespace {

template <int Bytes = sizeof(size_t)>
struct hash_conf;

template <>
struct hash_conf<4> {
  static constexpr uint32_t basis = 2166136261u;
  static constexpr uint32_t prime = 16777619u;
};

template <>
struct hash_conf<8> {
  static constexpr uint64_t basis = 14695981039346656037u;
  static constexpr uint64_t prime = 1099511628211u;
};

constexpr uint8_t static_bytes[] = {
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0xFF, 0xFF
};

constexpr size_t prehash(int i = 11) {
  return (i > 0)
    ? (prehash(i - 1) * hash_conf<>::prime) ^ static_bytes[i]
    : (hash_conf<>::basis * hash_conf<>::prime) ^ static_bytes[i];
}

} // namespace <anonymous>

namespace caf {
namespace io {
namespace network {

// hash for char*, see:
// - https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function
// - http://www.isthe.com/chongo/tech/comp/fnv/index.html
// Always hash 128 bit address, for v4 we use the embedded addr.
class ep_hash {
public:
  ep_hash();
  size_t operator()(const sockaddr_storage& sa) const noexcept;
  size_t hash(const sockaddr_in* sa) const noexcept;
  size_t hash(const sockaddr_in6* sa) const noexcept;
};

struct ip_endpoint {
  sockaddr_storage addr;
  socklen_t len;
};

bool operator==(const ip_endpoint& lhs, const ip_endpoint& rhs);

template <class Inspector>
typename Inspector::result_type inspect(Inspector& f, ip_endpoint& ep) {
  auto& sa = ep.addr;
  uint16_t port = 0;
  char addr[INET6_ADDRSTRLEN];
  switch(sa.ss_family) {
    case AF_INET:
      port = ntohs(reinterpret_cast<const sockaddr_in*>(&sa)->sin_port);
      inet_ntop(AF_INET,
                &reinterpret_cast<const sockaddr_in*>(&sa)->sin_addr,
                addr, INET_ADDRSTRLEN);
      break;
    case AF_INET6:
      port = ntohs(reinterpret_cast<const sockaddr_in6*>(&sa)->sin6_port);
      inet_ntop(AF_INET6,
                &reinterpret_cast<const sockaddr_in*>(&sa)->sin_addr,
                addr, INET6_ADDRSTRLEN);
      break;
    default:
      addr[0] = '\0';
      break;
  }
  return f(meta::type_name("ip_endpoint"), addr, port, ep.len);
}

std::string to_string(const ip_endpoint& ep);

std::string host(const ip_endpoint& ep);

uint16_t port(const ip_endpoint& ep);

} // namespace network
} // namespace io
} // namespace caf

namespace std {

template <>
struct hash<caf::io::network::ip_endpoint> {
  using argument_type = caf::io::network::ip_endpoint;
  using result_type = size_t;
  result_type operator()(const argument_type& ep) const {
    return caf::io::network::ep_hash{}(ep.addr);
  }
};

} // namespace std


#endif // CAF_IO_IP_ENDPOINT_HPP

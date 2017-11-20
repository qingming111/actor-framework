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

#ifndef CAF_IO_NETWORK_DGRAM_MANAGER_HPP
#define CAF_IO_NETWORK_DGRAM_MANAGER_HPP

#include "caf/io/dgram_handle.hpp"
#include "caf/io/network/manager.hpp"
#include "caf/io/network/receive_buffer.hpp"

namespace caf {
namespace io {
namespace network {

/// A datagram manager provides callbacks for outgoing
/// datagrams as well as for error handling.
class dgram_manager : public manager {
public:
  ~dgram_manager() override;

  /// Called by the underlying I/O device whenever it received data.
  /// @returns `true` if the manager accepts further reads, otherwise `false`.
  virtual bool consume(execution_unit*, dgram_handle hdl,
                       receive_buffer& buf) = 0;

  /// Called by the underlying I/O device whenever it sent data.
  virtual void datagram_sent(execution_unit*, dgram_handle hdl, size_t) = 0;

  /// Called by the underlying I/O device to indicate that a new remote
  /// endpoint has been detected, passing in the received datagram.
  /// @returns `true` if the manager accepts further enpoints,
  ///          otherwise `false`.
  virtual bool new_endpoint(receive_buffer& buf) = 0;

  /// Get the port of the underlying I/O device.
  virtual uint16_t port(dgram_handle) const = 0;
};

} // namespace network
} // namespace io
} // namespace caf

#endif // CAF_IO_NETWORK_DGRAM_MANAGER_HPP

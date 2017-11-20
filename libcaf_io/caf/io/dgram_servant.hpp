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

#ifndef CAF_IO_DGRAM_SERVANT_HPP
#define CAF_IO_DGRAM_SERVANT_HPP

#include <vector>

#include "caf/message.hpp"

#include "caf/io/dgram_handle.hpp"
#include "caf/io/broker_servant.hpp"
#include "caf/io/system_messages.hpp"
#include "caf/io/network/ip_endpoint.hpp"
#include "caf/io/network/dgram_manager.hpp"
#include "caf/io/network/receive_buffer.hpp"

namespace caf {
namespace io {

using dgram_servant_base = broker_servant<network::dgram_manager, dgram_handle,
                                          new_datagram_msg>;

/// Manages writing to a datagram sink.
/// @ingroup Broker
class dgram_servant : public dgram_servant_base {
public:
  dgram_servant(dgram_handle hdl);

  ~dgram_servant() override;

  /// Enables or disables write notifications.
  virtual void ack_writes(bool enable) = 0;

  /// Returns the current output buffer.
  virtual std::vector<char>& wr_buf(dgram_handle) = 0;

  /// Returns the current input buffer.
  virtual network::receive_buffer& rd_buf() = 0;

  /// Flushes the output buffer, i.e., sends the
  /// content of the buffer via the network.
  virtual void flush() = 0;

  /// Returns the local port of associated socket.
  virtual uint16_t local_port() const = 0;

  /// Returns all the handles associated with this servant
  virtual std::vector<dgram_handle> hdls() const = 0;

  /// Adds a new remote endpoint identified by the `ip_endpoint` to
  /// the related manager.
  virtual void add_endpoint(network::ip_endpoint& ep, dgram_handle hdl) = 0;

  virtual void remove_endpoint() = 0;

  void io_failure(execution_unit* ctx, network::operation op) override;

  bool consume(execution_unit*, dgram_handle hdl,
               network::receive_buffer& buf) override;

  void datagram_sent(execution_unit*, dgram_handle hdl, size_t) override;

  virtual void detach_handles() = 0;

  using dgram_servant_base::new_endpoint;

  virtual void launch() = 0;

protected:
  message detach_message() override;
};

using dgram_servant_ptr = intrusive_ptr<dgram_servant>;

} // namespace io
} // namespace caf

// Allows the `middleman_actor` to create an `dgram_servant` and then send it
// to the BASP broker.
CAF_ALLOW_UNSAFE_MESSAGE_TYPE(caf::io::dgram_servant_ptr)

#endif // CAF_IO_DGRAM_SERVANT_HPP

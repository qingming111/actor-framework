#include <string>
#include <iostream>

#include "caf/all.hpp"

#include "caf/intrusive/bidirectional_iterator.hpp"

#include "caf/test/unit_test.hpp"
#include "caf/test/unit_test_impl.hpp"

using std::endl;
using std::string;

namespace caf {
namespace intrusive {

template <class T, class Delete = std::default_delete<T>>
class doubly_linked_list {
public:
  using value_type = T;

  using deleter_type = Delete;

  using pointer = value_type*;

  using const_pointer = const value_type*;

  using reference = value_type&;

  using const_reference = const value_type&;

  using unique_pointer = std::unique_ptr<value_type, deleter_type>;

  using dummy_type = typename T::dummy_type;

  using dummy_pointer = dummy_type*;

  using iterator = bidirectional_iterator<T>;

  using const_iterator = bidirectional_iterator<const T>;

  doubly_linked_list() noexcept
    : size_(0),
      head_(&tail_),
      tail_(nullptr, &head_) {
    // nop
  }

  ~doubly_linked_list() noexcept {
    clear();
  }

  iterator begin() noexcept {
    return head_.next;
  }

  const_iterator begin() const noexcept {
    return head_.next;
  }

  const_iterator cbegin() const noexcept {
    return head_.next;
  }

  iterator end() noexcept {
    return &tail_;
  }

  const_iterator end() const noexcept {
    return &tail_;
  }

  const_iterator cend() const noexcept {
    return &tail_;
  }

  /// Removes all nodes from the list after calling `f` on each element.
  template <class F>
  void clear(F f) {
    for (auto i = begin(); i != end();) {
      auto ptr = promote(i.ptr);
      ++i;
      f(*ptr);
      delete_(ptr);
    }
    size_ = 0;
    head_.next = &tail_;
    tail_.prev = &head_;
  }

  /// Removes all nodes from the list.
  void clear() noexcept {
    auto nop = [](value_type&) {};
    clear(nop);
  }

  /// @pre `!empty()`
  reference front() noexcept {
    return *begin();
  }

  /// @pre `!empty()`
  void pop_front() noexcept {
    erase(begin());
  }

  /// @pre `!empty()`
  reference back() noexcept {
    return *promote(tail_.prev);
  }

  /// @pre `!empty()`
  void pop_back() noexcept {
    erase(tail_.prev);
  }

  /// Inserts `val` as new element before `next`.
  iterator insert(iterator next, pointer val) {
    auto prev = next->prev;
    val->prev = prev;
    val->next = next.ptr;
    prev->next = val;
    next->prev = val;
    ++size_;
    return val;
  }

  /// Constructs a new element in-place and inserts it before `next`.
  template <class... Ts>
  iterator emplace(iterator next, Ts&&... xs) {
    return insert(next, new value_type(std::forward<Ts>(xs)...));
  }

  /// Constructs a new element in-place and prepends it.
  template <class... Ts>
  iterator emplace_front(Ts&&... xs) {
    return emplace(begin(), std::forward<Ts>(xs)...);
  }
  /// Constructs a new element in-place and appends it.
  template <class... Ts>
  iterator emplace_back(Ts&&... xs) {
    return emplace(end(), std::forward<Ts>(xs)...);
  }

  bool empty() const noexcept {
    return size_ == 0;
  }

  /// Takes a node out of the list and returns it.
  unique_pointer take(iterator pos) noexcept {
    unique_pointer res{promote(pos.ptr)};
    auto next = res->next;
    auto prev = res->prev;
    prev->next = next;
    next->prev = prev;
    --size_;
    return res;
  }

  iterator erase(iterator pos) {
    auto next = pos->next;
    take(pos);
    return next;
  }

  unique_pointer take_front() {
    unique_pointer result;
    if (!empty())
      result = take(begin());
    return result;
  }

  size_t size() const {
    return size_;
  }

private:
  size_t size_;
  dummy_type head_;
  dummy_type tail_;
  deleter_type delete_;
};

template <class T, class DT, class U, class DU>
bool operator==(const doubly_linked_list<T, DT>& xs,
                const doubly_linked_list<U, DU>& ys) {
  return xs.size() == ys.size()
         && std::equal(xs.begin(), xs.end(), ys.begin());
}

template <class T, class DT, class U, class DU>
bool operator!=(const doubly_linked_list<T, DT>& xs,
                const doubly_linked_list<U, DU>& ys) {
  return !(xs == ys);
}

using mbox = doubly_linked_list<mailbox_element, detail::disposer>;

/// A DWRR queue with deficit counter.
template <class Policy>
struct dwrr_queue {

  using policy_type = Policy;

  using value_type = typename policy_type::mapped_type;

  using dummy_type = typename value_type::dummy_type;

  using pointer = value_type*;

  using const_pointer = const value_type*;

  using reference = value_type&;

  using const_reference = const value_type&;

  using unique_pointer = typename policy_type::unique_pointer;

  using deficit_type = typename policy_type::deficit_type;

  using task_size_type = typename policy_type::task_size_type;

  template <class... Ts>
  dwrr_queue(Ts&&... xs)
      : deficit_(0),
        total_task_size_(0),
        policy_(std::forward<Ts>(xs)...) {
    init();
  }

  dwrr_queue(dwrr_queue&& other) : dwrr_queue(other.policy_) {
    if (!other.empty()) {
      head_.next = other.head_.next;
      tail_.next = other.tail_.next;
      tail_.next->next = &tail_;
      other.init();
    }
  }

  ~dwrr_queue() {
    for (auto i = head_.next; i != &tail_;) {
      auto ptr = i;
      i = i->next;
      policy_.release(promote(ptr));
    }
  }

  bool empty() const {
    return head_.next == &tail_;
  }

  void push_back(pointer ptr) {
    auto last = tail_.next;
    last->next = ptr;
    ptr->next = &tail_;
    tail_.next = ptr;
    total_task_size_ += policy_.task_size(*ptr);
  }

  void push_back(unique_pointer ptr) {
    push_back(ptr.release());
  }

  template <class... Ts>
  void emplace_back(Ts&&... xs) {
    push_back(new value_type(std::forward<Ts>(xs)...));
  }

  unique_pointer take_front() {
    unique_pointer result;
    if (!empty()) {
      auto ptr = head_.next;
      auto ts = policy_.task_size(*promote(ptr));
      if (ts <= deficit_) {
        deficit_ -= ts;
        total_task_size_ -= ts;
        head_.next = ptr->next;
        if (head_.next == &tail_) {
          CAF_ASSERT(total_task_size_ == 0);
          deficit_ = 0;
          tail_.next = &head_;
        }
        result.reset(promote(ptr));
      }
    }
    return result;
  }

  task_size_type total_task_size() const {
    return total_task_size_;
  }

  deficit_type deficit() const {
    return deficit_;
  }

  void inc_deficit(deficit_type x) {
    if (!empty())
      deficit_ += x;
  }

private:
  void init() {
    head_.next = &tail_;
    tail_.next = &head_;
  }

  /// Dummy element pointing to the first element.
  dummy_type head_;

  /// Dummy element pointing past the last element.
  dummy_type tail_;

  /// Stores the deficit on this queue.
  deficit_type deficit_ = 0;

  /// Stores the total size of all items in the queue.
  task_size_type total_task_size_ = 0;

  /// Manipulates instances of T.
  policy_type policy_;
};

/// A work queue that internally multiplexes any number of DWRR-managed queues.
template <class Policy>
class dwrr_multiplexed_queue {
public:
  using policy_type = Policy;

  using queue_type = dwrr_queue<policy_type>;

  using key_type = typename Policy::key_type;

  using mapped_type = typename policy_type::mapped_type;

  using unique_pointer = typename policy_type::unique_pointer;

  using value_type = std::pair<const key_type, queue_type>;

  /// Stores active and non-active queues.
  using queue_container_type = std::vector<value_type>;

  /// Stores a position in the queue list.
  using queue_container_index = typename queue_container_type::size_type;

  template <class... Ts>
  dwrr_multiplexed_queue(Ts&&... xs) : policy_(std::forward<Ts>(xs)...) {
    // nop
  }

  /*
  template <class F>
  size_t consume(size_t n, F f) {
    auto start = pos_;
    for (size_t i = 0; i < n; ++i) {
      auto ptr = qs_[pos_].second.take_front();
      while (ptr == nullptr) {
        // Go to the next queue and stop if we did a full round.
        pos_ = (pos_ + 1) % qs_.size();
        if (pos_ == start)
          return i;
        ptr = qs_[pos_].second.take_front();
      }
      f(qs_[pos_].first, *ptr);
    }
    return n;
  }
  */

  void push_back(mapped_type* ptr) {
    auto id = policy_.id_of(*ptr);
    auto i = find(id);
    if (i != qs_.end()) {
      i->second.push_back(ptr);
    } else {
      auto opt_id = policy_.make_queue_id(*ptr);
      if (opt_id) {
        qs_.emplace_back(std::move(*opt_id), queue_type{policy_});
        qs_.back().second.push_back(ptr);
      }
    } 
  }

  template <class... Ts>
  void emplace_back(Ts&&... xs) {
    push_back(new mapped_type(std::forward<Ts>(xs)...));
  }

  unique_pointer take_front() {
    unique_pointer result;
    if (!empty()) {
      auto i = rr_pos_;
      result = qs_[i].second.take_front();
      if (result == nullptr) {
        auto e = qs_.size();
        auto next = [e](queue_container_index x) {
          return (x + 1) % e;
        };
        for (i = next(i); i != rr_pos_; i = next(i)) {
          result = qs_[i].second.take_front();
          if (result != nullptr) {
            rr_pos_ = i;
            break;
          }
        }
      }
    }
    return result;
  }


  void new_round(long quantum) {
    // TODO: weighted
    for (auto& q : qs_)
      q.second.inc_deficit(quantum);
  }

  void erase(const key_type& x) {
    auto i = find(x);
    if (i != qs_.end()) {
      if (static_cast<ptrdiff_t>(rr_pos_) > std::distance(qs_.begin(), i))
        --rr_pos_;
      qs_.erase(i);
    }
  }

  bool empty() const {
    auto is_empty = [](const value_type& q) {
      return q.second.empty();
    };
    return std::all_of(qs_.begin(), qs_.end(), is_empty);
  }

private:
  template <class K>
  typename std::vector<value_type>::iterator find(const K& x) {
    auto pred = [&](const value_type& y) {
      return x == y.first;
    };
    return std::find_if(qs_.begin(), qs_.end(), pred);
  }

  /// All queues.
  queue_container_type qs_;

  queue_container_index rr_pos_;

  Policy policy_;
};

struct dwrr_policy {
  dwrr_policy(scheduled_actor* self) : self_(self) {
    // nop
  }

  dwrr_policy(const dwrr_policy&) = default;

  using mapped_type = mailbox_element;

  using task_size_type = long;

  using deficit_type = long;

  using unique_pointer = std::unique_ptr<mailbox_element, detail::disposer>;

  static inline void release(mailbox_element* ptr) {
    detail::disposer d;
    d(ptr);
  }

  static inline long task_size(const mailbox_element& x) {
    auto& sm = x.content().get_as<stream_msg>(0);
    if (holds_alternative<stream_msg::batch>(sm.content))
      return get<stream_msg::batch>(sm.content).xs_size;
    return 0l;
  }

  struct key_type {
    stream_id sid;
    strong_actor_ptr source;
    stream_manager_ptr manager;
  };

  using lookup_type = std::pair<stream_id, actor_addr>;

  static optional<key_type> make_queue_id(const mailbox_element& x) {
    auto& sm = x.content().get_as<stream_msg>(0);
    auto src = actor_cast<strong_actor_ptr>(sm.sender);
    if (src != nullptr)
      return key_type{sm.sid, src, nullptr};
    return none;
  }

  static lookup_type id_of(const mailbox_element& x) {
    auto& sm = x.content().get_as<stream_msg>(0);
    return {sm.sid, sm.sender};
  }

private:
  scheduled_actor* self_;
};

bool operator==(const dwrr_policy::key_type& x,
                const dwrr_policy::lookup_type& y) {
  return x.sid == y.first && x.source == y.second;
}

bool operator==(const dwrr_policy::lookup_type& x,
                const dwrr_policy::key_type& y) {
  return y == x;
}

class dwrr_tester : public event_based_actor {
public:
  using super = event_based_actor;

  dwrr_tester(actor_config& cfg) : event_based_actor(cfg), dc_(this) {
    // nop
  }

  resumable::resume_result resume(execution_unit* ctx,
                                  size_t max_throughput) override {
    CAF_PUSH_AID(id());
    auto handle_sm = [&](const dwrr_policy::key_type&,
                         mailbox_element&) {
      // TODO: implement me
    };
    if (!activate(ctx))
      return resume_result::done;
    size_t handled_msgs = 0;
    auto reset_timeout_if_needed = [&] {
      if (handled_msgs > 0 && !bhvr_stack_.empty())
        request_timeout(bhvr_stack_.back().timeout());
    };
    for (;;) {
      if (mb_.empty())
        while (!fetch()) {
          if (mailbox_.try_block())
            return resumable::awaiting_message;
        }
      /*
      handled_msgs += dc_.consume(max_throughput - handled_msgs, handle_sm);
      auto ptr = mb_.take_front();
      while (ptr != nullptr) {
        switch (reactivate(*ptr)) {
          case activation_result::terminated:
            return resume_result::done;
          case activation_result::success:
            ++handled_msgs;
            // iterate cache to see if we are now able
            // to process previously skipped messages
            while (consume_from_cache()) {
              ++handled_msgs;
              bhvr_stack_.cleanup();
              if (finalize()) {
                CAF_LOG_DEBUG("actor finalized while processing cache");
                return resume_result::done;
              }
            }
            if (handled_msgs >= max_throughput) {
              // Time's up.
              reset_timeout_if_needed();
              if (dc_.empty() && mb_.empty() && mailbox().try_block())
                return resumable::awaiting_message;
              return resumable::resume_later;
            }
            break;
          case activation_result::skipped:
            push_to_cache(std::move(ptr));
            break;
          default:
            break;
        }
        ptr = mb_.take_front();
      }
      */
    }
  }

private:
  bool fetch() {
    auto ptr = mailbox_.take_stack();
    if (ptr != nullptr) {
      auto x = ptr;
      ptr = promote(ptr->next);
      if (!x->content().match_elements<stream_msg>()) {
        mb_.insert(mb_.end(), x);
      } else {
        dc_.push_back(x);
      }
      return true;
    }
    return false;
  }

  using dwrr_mbox = dwrr_multiplexed_queue<dwrr_policy>;

  dwrr_mbox dc_;
  mbox mb_;
};

} // namespace intrusive
} // namespace caf

using namespace caf;
using namespace caf::intrusive;

namespace {

struct inode : doubly_linked<inode> {
  int value;
  inode(int x = 0) : value(x) {
    // nop
  }
};

template <class Inspector>
typename Inspector::result_type inspect(Inspector& f, inode& x) {
  return f(x.value);
}

inline bool operator==(const inode& x, const inode& y) {
  return x.value == y.value;
}

inline bool operator==(int x, const inode& y) {
  return x == y.value;
}

inline bool operator==(const inode& x, int y) {
  return (y == x);
}

} // namespace <anonymous>

CAF_TEST(doubly_linked_list) {
  doubly_linked_list<inode> l1;
  doubly_linked_list<inode> l2;
  CAF_REQUIRE(l1.empty());
  CAF_REQUIRE_EQUAL(l1.size(), 0u);
  CAF_REQUIRE_EQUAL(l1, l2);
  l1.emplace_front(3);
  l1.emplace_front(2);
  l1.emplace_front(1);
  l2.emplace_back(1);
  l2.emplace_back(2);
  l2.emplace_back(3);
  CAF_REQUIRE_EQUAL(l1, l2);
  CAF_REQUIRE_EQUAL(l1.front(), 1);
  CAF_REQUIRE_EQUAL(l1.back(), 3);
  CAF_REQUIRE_EQUAL(deep_to_string(l1), "[1, 2, 3]");
  l2.erase(++l2.begin());
  CAF_REQUIRE_EQUAL(deep_to_string(l2), "[1, 3]");
  CAF_REQUIRE_NOT_EQUAL(l1, l2);
  l2.pop_front();
  CAF_REQUIRE_EQUAL(deep_to_string(l2), "[3]");
  l2.pop_back();
  CAF_REQUIRE_EQUAL(deep_to_string(l2), "[]");
  CAF_REQUIRE_EQUAL(l2.size(), 0u);
}

namespace {

/// A simple policy for testing DWRR queues. The task size for each element is
/// equal to its value.
struct simple_ipolicy {
  using mapped_type = inode;

  using task_size_type = int;

  using deficit_type = int;

  using unique_pointer = std::unique_ptr<inode>;

  static inline void release(mapped_type* ptr) {
    delete ptr;
  }

  static inline task_size_type task_size(const mapped_type& x) {
    return x.value;
  }
};

} // namespace <anonymous>

CAF_TEST(single_dwrr_queue) {
  dwrr_queue<simple_ipolicy> q;
  // A default-constructed queue is empty.
  CAF_REQUIRE_EQUAL(q.empty(), true);
  CAF_REQUIRE_EQUAL(q.deficit(), 0);
  // Increasing the deficit does nothing if the queue is empty.
  q.inc_deficit(100);
  CAF_REQUIRE_EQUAL(q.deficit(), 0);
  // Fill in values.
  for (int i = 1; i <= 100; ++i)
    q.emplace_back(i);
  // The queue is not empty but we can't dequeue from it.
  CAF_REQUIRE_EQUAL(q.empty(), false);
  CAF_REQUIRE_EQUAL(q.take_front(), nullptr);
  // Add 45 deficit and dequeue the numbers 1-9.
  q.inc_deficit(45);
  CAF_REQUIRE_EQUAL(q.deficit(), 45);
  std::vector<int> expected{1, 2, 3, 4, 5, 6, 7, 8, 9};
  std::vector<int> buf;
  auto ptr = q.take_front();
  while (ptr != nullptr) {
    buf.emplace_back(ptr->value);
    ptr = q.take_front();
  }
  CAF_REQUIRE_EQUAL(q.deficit(), 0);
  CAF_REQUIRE_EQUAL(buf, expected);
}

namespace {

/// Dispatches based on `value % 3`. Task sizes are always 1.
struct mod3_ipolicy {
  using mapped_type = inode;

  using key_type = int;

  using task_size_type = int;

  using deficit_type = int;

  using unique_pointer = std::unique_ptr<inode>;

  optional<key_type> make_queue_id(const mapped_type& x) {
    return x.value % 3;
  }

  key_type id_of(const mapped_type& x) {
    return x.value % 3;
  }

  static inline void release(mapped_type* ptr) {
    delete ptr;
  }

  static constexpr task_size_type task_size(const mapped_type&) {
    return 1;
  }
};

} // namespace <anonymous>

CAF_TEST(multiplexed_dwrr_queue) {
  dwrr_multiplexed_queue<mod3_ipolicy> q;
  // A default-constructed queue is empty.
  CAF_REQUIRE_EQUAL(q.empty(), true);
  // Fill in values.
  for (int i = 1; i <= 100; ++i)
    q.emplace_back(i);
  CAF_REQUIRE_EQUAL(q.empty(), false);
  // Give each queue a deficit of 3 and read for as long as possible.
  q.new_round(9);
  std::vector<int> expected{3, 6, 9, 2, 5, 8, 1, 4, 7};
  std::vector<int> buf;
  auto ptr = q.take_front();
  while (ptr != nullptr) {
    buf.emplace_back(ptr->value);
    ptr = q.take_front();
  }
  CAF_REQUIRE_EQUAL(buf, expected);
}

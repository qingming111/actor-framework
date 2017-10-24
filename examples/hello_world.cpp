#include <string>
#include <iostream>

#include "caf/all.hpp"

//#include "caf/test/unit_test.hpp"
//#include "caf/test/unit_test_impl.hpp"

// Google Benchmark Library
#include <benchmark/benchmark.h>

#include <boost/spirit/home/qi.hpp>

#include <boost/fusion/include/std_pair.hpp>
#include <boost/spirit/include/qi_char_class.hpp>
#include <boost/spirit/include/qi_int.hpp>

using std::cout;
using std::endl;
using std::string;

using namespace caf;

/*
constexpr int64_t zero = 0;

CAF_TEST(fixed_ints) {
  int64_t st;
  auto p0 = parser_tester(st, int3_[assign(st)]);
  CAF_CHECK_EQUAL(p0(""), none);
  CAF_CHECK_EQUAL(p0("1"), none);
  CAF_CHECK_EQUAL(p0("12"), none);
  CAF_CHECK_EQUAL(p0("123"), int64_t{123});
  CAF_CHECK_EQUAL(p0("1234"), none);
  CAF_CHECK_EQUAL(p0("12345"), none);
  CAF_CHECK_EQUAL(p0("123456"), none);
  using ints = std::vector<int64_t>;
  ints xs;
  auto p1 = parser_tester(xs, +(int3_[emplace_back(xs)]));
  ints _123{123};
  ints _123456{123, 456};
  CAF_CHECK_EQUAL(p1(""), none);
  CAF_CHECK_EQUAL(p1("1"), none);
  CAF_CHECK_EQUAL(p1("12"), none);
  CAF_CHECK_EQUAL(p1("123"), _123);
  CAF_CHECK_EQUAL(p1("1234"), none);
  CAF_CHECK_EQUAL(p1("12345"), none);
  CAF_CHECK_EQUAL(p1("123456"), _123456);
}

CAF_TEST(integers) {
  int64_t st;
  auto p = parser_tester(st, int_[assign(st)]);
  //single<integer<int64_t>, std::reference_wrapper<int64_t>> sp{std::ref(st)};
  //auto p = parser_tester(st, sp);
  //auto p = parser_tester(st, lift<integer>(st));
  CAF_CHECK_EQUAL(p("0"), zero);
  CAF_CHECK_EQUAL(p("1"), int64_t{1});
  CAF_CHECK_EQUAL(p("10"), int64_t{10});
  CAF_CHECK_EQUAL(p("999"), int64_t{999});
  CAF_CHECK_EQUAL(p("999f"), none);
  CAF_CHECK_EQUAL(p("999s"), none);
  CAF_CHECK_EQUAL(p(" 0"), none);
  CAF_CHECK_EQUAL(p("0 "), none);
  CAF_CHECK_EQUAL(p(" 0 "), none);
}

CAF_TEST(integers_with_spaces) {
  integer_storage st;
  //auto ws = lift<whitespace>(st);
  single<literal<integer_storage, ' '>> ws;
  single<integer<integer_storage>> in;
  auto p1 = parser_tester(st, *ws >> in);
  CAF_CHECK_EQUAL(p1("0"), zero);
  CAF_CHECK_EQUAL(p1("1"), int64_t{1});
  CAF_CHECK_EQUAL(p1("10"), int64_t{10});
  CAF_CHECK_EQUAL(p1("999"), int64_t{999});
  CAF_CHECK_EQUAL(p1(" 0"), zero);
  CAF_CHECK_EQUAL(p1("  1"), int64_t{1});
  CAF_CHECK_EQUAL(p1("   10"), int64_t{10});
  CAF_CHECK_EQUAL(p1("    999"), int64_t{999});
  CAF_CHECK_EQUAL(p1("0 "), none);
  CAF_CHECK_EQUAL(p1("1  "), none);
  CAF_CHECK_EQUAL(p1("10   "), none);
  CAF_CHECK_EQUAL(p1("999    "), none);
  CAF_CHECK_EQUAL(p1("   0"), zero);
  CAF_CHECK_EQUAL(p1("  1 "), none);
  CAF_CHECK_EQUAL(p1(" 10 "), none);
  CAF_CHECK_EQUAL(p1("999 "), none);
  CAF_CHECK_EQUAL(p1("999f"), none);
  CAF_CHECK_EQUAL(p1("999s"), none);
  auto p2 = parser_tester(st, in >> *ws);
  CAF_CHECK_EQUAL(p2("0"), zero);
  CAF_CHECK_EQUAL(p2("1"), int64_t{1});
  CAF_CHECK_EQUAL(p2("10"), int64_t{10});
  CAF_CHECK_EQUAL(p2("999"), int64_t{999});
  CAF_CHECK_EQUAL(p2(" 0"), none);
  CAF_CHECK_EQUAL(p2("  1"), none);
  CAF_CHECK_EQUAL(p2("   10"), none);
  CAF_CHECK_EQUAL(p2("    999"), none);
  CAF_CHECK_EQUAL(p2("0 "), zero);
  CAF_CHECK_EQUAL(p2("1  "), int64_t{1});
  CAF_CHECK_EQUAL(p2("10   "), int64_t{10});
  CAF_CHECK_EQUAL(p2("999    "), int64_t{999});
  CAF_CHECK_EQUAL(p2("   0"), none);
  CAF_CHECK_EQUAL(p2("  1 "), none);
  CAF_CHECK_EQUAL(p2(" 10 "), none);
  CAF_CHECK_EQUAL(p2("999 "), int64_t{999});
  CAF_CHECK_EQUAL(p2("999f"), none);
  CAF_CHECK_EQUAL(p2("999s"), none);
  auto p3 = parser_tester(st, *ws >> in >> *ws);
  CAF_CHECK_EQUAL(p3("0"), zero);
  CAF_CHECK_EQUAL(p3("1"), int64_t{1});
  CAF_CHECK_EQUAL(p3("10"), int64_t{10});
  CAF_CHECK_EQUAL(p3("999"), int64_t{999});
  CAF_CHECK_EQUAL(p3(" 0"), zero);
  CAF_CHECK_EQUAL(p3("  1"), int64_t{1});
  CAF_CHECK_EQUAL(p3("   10"), int64_t{10});
  CAF_CHECK_EQUAL(p3("    999"), int64_t{999});
  CAF_CHECK_EQUAL(p3("0 "), zero);
  CAF_CHECK_EQUAL(p3("1  "), int64_t{1});
  CAF_CHECK_EQUAL(p3("10   "), int64_t{10});
  CAF_CHECK_EQUAL(p3("999    "), int64_t{999});
  CAF_CHECK_EQUAL(p3("   0"), zero);
  CAF_CHECK_EQUAL(p3("  1 "), int64_t{1});
  CAF_CHECK_EQUAL(p3(" 10 "), int64_t{10});
  CAF_CHECK_EQUAL(p3("999 "), int64_t{999});
  CAF_CHECK_EQUAL(p3("999f"), none);
  CAF_CHECK_EQUAL(p3("999s"), none);
  auto p4 = parser_tester(st, +ws >> in);
  CAF_CHECK_EQUAL(p4(""), none);
  CAF_CHECK_EQUAL(p4(" 2"), int64_t{2});
  CAF_CHECK_EQUAL(p4(" 2 3"), none);
  auto p5 = parser_tester(st, *(+ws >> in));
  CAF_CHECK_EQUAL(p5(""), int64_t{0});
  CAF_CHECK_EQUAL(p5(" 2"), int64_t{2});
  CAF_CHECK_EQUAL(p5(" 2 3"), int64_t{3});
  auto p6 = parser_tester(st, in >> *(+ws >> in));
  CAF_CHECK_EQUAL(p6("1"), int64_t{1});
  CAF_CHECK_EQUAL(p6("1 2"), int64_t{2});
  CAF_CHECK_EQUAL(p6("1 2 3"), int64_t{3});
}

CAF_TEST(literals) {
  integer_storage st;
  single<literal<integer_storage, 'a', 'b', 'c'>> abc;
  auto p0 = parser_tester(st, abc);
  CAF_CHECK_EQUAL(p0(""), none);
  CAF_CHECK_EQUAL(p0("a"), none);
  CAF_CHECK_EQUAL(p0("ab"), none);
  CAF_CHECK_EQUAL(p0("abc"), zero);
  CAF_CHECK_EQUAL(p0("cba"), none);
  CAF_CHECK_EQUAL(p0("abcd"), none);
  CAF_CHECK_EQUAL(p0("abcabc"), none);
  auto p1 = parser_tester(st, *abc);
  CAF_CHECK_EQUAL(p1(""), zero);
  CAF_CHECK_EQUAL(p1("a"), none);
  CAF_CHECK_EQUAL(p1("ab"), none);
  CAF_CHECK_EQUAL(p1("abc"), zero);
  CAF_CHECK_EQUAL(p1("cba"), none);
  CAF_CHECK_EQUAL(p1("abcd"), none);
  CAF_CHECK_EQUAL(p1("abcabc"), zero);
  auto p2 = parser_tester(st, +abc);
  CAF_CHECK_EQUAL(p2(""), none);
  CAF_CHECK_EQUAL(p2("a"), none);
  CAF_CHECK_EQUAL(p2("ab"), none);
  CAF_CHECK_EQUAL(p2("abc"), zero);
  CAF_CHECK_EQUAL(p2("cba"), none);
  CAF_CHECK_EQUAL(p2("abcd"), none);
  CAF_CHECK_EQUAL(p2("abcabc"), zero);
  auto p3 = parser_tester(st, abc >> abc);
  CAF_CHECK_EQUAL(p3(""), none);
  CAF_CHECK_EQUAL(p3("a"), none);
  CAF_CHECK_EQUAL(p3("ab"), none);
  CAF_CHECK_EQUAL(p3("abc"), none);
  CAF_CHECK_EQUAL(p3("cba"), none);
  CAF_CHECK_EQUAL(p3("abcd"), none);
  CAF_CHECK_EQUAL(p3("abcabc"), zero);
  CAF_CHECK_EQUAL(p3("abcabcabc"), none);
  auto p4 = parser_tester(st, +(abc >> abc));
  CAF_CHECK_EQUAL(p4(""), none);
  CAF_CHECK_EQUAL(p4("a"), none);
  CAF_CHECK_EQUAL(p4("ab"), none);
  CAF_CHECK_EQUAL(p4("abc"), none);
  CAF_CHECK_EQUAL(p4("cba"), none);
  CAF_CHECK_EQUAL(p4("abcd"), none);
  CAF_CHECK_EQUAL(p4("abcabc"), zero);
  CAF_CHECK_EQUAL(p4("abcabcab"), none);
  CAF_CHECK_EQUAL(p4("abcabcabcabc"), zero);
  auto p5 = parser_tester(st, *(abc >> abc));
  CAF_CHECK_EQUAL(p5(""), zero);
  CAF_CHECK_EQUAL(p5("a"), none);
  CAF_CHECK_EQUAL(p5("ab"), none);
  CAF_CHECK_EQUAL(p5("abc"), none);
  CAF_CHECK_EQUAL(p5("cba"), none);
  CAF_CHECK_EQUAL(p5("abcd"), none);
  CAF_CHECK_EQUAL(p5("abcabc"), zero);
  CAF_CHECK_EQUAL(p5("abcabcab"), none);
  CAF_CHECK_EQUAL(p5("abcabcabcabc"), zero);
}

CAF_TEST(integer_list) {
  integer_storage st;
  single<integer<integer_storage>> num;
  single<literal<integer_storage, ','>> sep;
  auto p = parser_tester(st, num >> *(sep >> num));
  CAF_CHECK_EQUAL(p("0"), zero);
  CAF_CHECK_EQUAL(p("a"), none);
  CAF_CHECK_EQUAL(p("1,2"), int64_t{2});
  CAF_CHECK_EQUAL(p("1,2,3"), int64_t{3});
  CAF_CHECK_EQUAL(p("1,a,3"), none);
  CAF_CHECK_EQUAL(p(",3"), none);
}
*/

#define start(name)                                                            \
  ec default_error;                                                            \
  goto s_##name;                                                               \
  s_return_from_fsm:

#define state(name)                                                            \
  return {i, default_error};                                                   \
  s_##name : __attribute__((unused));                                          \
  if (i == last)                                                               \
    return {i, ec::unexpected_eof};                                            \
  e_##name : __attribute__((unused));                                          \
  default_error = ec::invalid_character;

#define term_state(name)                                                       \
  return {i, default_error};                                                   \
  s_##name : __attribute__((unused));                                          \
  if (i == last)                                                               \
    return {i, ec::none};                                                      \
  e_##name : __attribute__((unused));                                          \
  default_error = ec::none;
  //default_error = ec::trailing_character;

#define input(condition, target)                                               \
  if (condition) {                                                             \
    ++i;                                                                       \
    goto s_##target;                                                           \
  }

#define action(condition, target, statement)                                   \
  if (condition) {                                                             \
    statement;                                                                 \
    ++i;                                                                       \
    goto s_##target;                                                           \
  }

#define epsilon(target) goto e_##target;

#define stop() goto s_return_from_fsm;

enum class ec {
  /// Not-an-error.
  none,

  /// Parser stopped after reaching the end while still expecting input.
  unexpected_eof,

  /// Parser stopped after reading an unexpected character.
  invalid_character,
};

const char* ec_names[] = {
  "none",
  "unexpected_eof",
  "invalid_character",
};

std::string to_string(ec x) {
  return ec_names[static_cast<int>(x)];
}

template <class T>
struct integer {
  using value_type = T;

  static inline T hexval(char c) {
    return c >= '0' && c <= '9'
           ? c - '0'
           : (c >= 'A' && c <= 'F' ? c - 'A' : c - 'a') + 10;
  }

  static inline bool bin_digit(char c) {
    return c == '0' || c == '1';
  }

  static inline bool oct_digit(char c) {
    return c >= '0' && c <= '7';
  }

  static inline bool dec_digit(char c) {
    return c >= '0' && c <= '9';
  }

  static inline bool hex_digit(char c) {
    return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')
           || (c >= 'A' && c <= 'F');
  }

  template <class Iterator, class Sentinel>
  static std::pair<Iterator, ec> run(T& x, Iterator i, Sentinel last) {
    start(init);
    state(init) {
      input(*i == '-', start_neg)
      action(*i == '0', pos_zero, x = 0)
      action(dec_digit(*i), pos_dec, x = *i - '0')
    }
    term_state(pos_zero) {
      input(*i == 'b' || *i == 'B', start_pos_bin)
      input(*i == 'x' || *i == 'X', start_pos_hex)
      action(oct_digit(*i), pos_oct, x = *i - '0')
    }
    state(start_neg) {
      action(*i == '0', neg_zero, x = 0)
      action(dec_digit(*i), neg_dec, x = -(*i - '0'))
    }
    term_state(neg_zero) {
      input(*i == 'b' || *i == 'B', start_neg_bin)
      input(*i == 'x' || *i == 'X', start_pos_hex)
      action(oct_digit(*i), pos_oct, x = -(*i - '0'))
    }
    state(start_pos_bin) {
      epsilon(pos_bin)
    }
    term_state(pos_bin) {
      action(bin_digit(*i), pos_bin, x = (x * 2) + (*i - '0'))
    }
    term_state(pos_oct) {
      action(oct_digit(*i), pos_oct, x = (x * 8) + (*i - '0'))
    }
    term_state(pos_dec) {
      action(dec_digit(*i), pos_dec, x = (x * 10) + (*i - '0'))
    }
    state(start_pos_hex) {
      epsilon(pos_hex)
    }
    term_state(pos_hex) {
      action(hex_digit(*i), pos_hex, x = (x * 16) + hexval(*i))
    }
    state(start_neg_bin) {
      epsilon(neg_bin)
    }
    term_state(neg_bin) {
      action(bin_digit(*i), neg_bin, x = (x * 2) - (*i - '0'))
    }
    state(neg_oct) {
      action(oct_digit(*i), neg_oct, x = (x * 8) - (*i - '0'))
    }
    term_state(neg_dec) {
      action(dec_digit(*i), neg_dec, x = (x * 10) - (*i - '0'))
    }
    state(start_neg_hex) {
      epsilon(neg_hex)
    }
    term_state(neg_hex) {
      action(hex_digit(*i), neg_hex, x = (x * 16) - (hexval(*i)))
    }
    stop();
  }
};

struct unit_v {
  static constexpr unit_t value = unit;
};

struct parser_tag {};

template <class T>
struct is_parser : std::is_base_of<parser_tag, T> {};

template <class Impl, class Token = unit_v>
class single : public parser_tag {
public:
  using token = Token;

  using impl = Impl;

  using value_type = typename impl::value_type;

  constexpr single() {
    // nop
  }

  template <class Consumer, class Iterator, class Sentinel>
  std::pair<Iterator, ec> parse(Consumer& consumer, value_type& x,
                                Iterator first, Sentinel last) {
    auto res = impl::run(x, first, last);
    if (res.second == ec::none)
      consumer.value(Token::value, std::move(x));
    return res;
  }

  template <class Consumer, class Iterator>
  std::pair<Iterator, ec> parse(Consumer& consumer, Iterator first,
                                Iterator last) {
    value_type x;
    return parse(consumer, x, first, last);
  }

  template <class NewToken>
  constexpr single<Impl, NewToken> operator[](NewToken) const {
    return {};
  }
};

template <class Parser, class Token = unit_v>
class one_or_more : public parser_tag {
public:
  using token = Token;

  using value_token = typename Parser::token;

  using value_type = typename Parser::value_type;

  constexpr one_or_more() {
    // nop
  }

  constexpr one_or_more(Parser x) : p_(std::move(x)) {
    // nop
  }

  template <class Consumer, class Iterator, class Sentinel>
  std::pair<Iterator, ec> parse(Consumer& consumer, value_type& x,
                                Iterator first, Sentinel last) {
    if (first == last)
      return {first, ec::unexpected_eof};
    consumer.begin_sequence(token::value);
    auto res = p_.parse(consumer, x, first, last);
    if (res.second != ec::none) {
      return res;
    }
    decltype(res) last_res;
    // try again until p_ stops
    do {
      x = 0; // TODO: make generic
      last_res = res;
      res = p_.parse(consumer, x, res.first, last);
    } while (res.second != ec::none);
    consumer.end_sequence(token::value);
    return last_res;
  }

  template <class Consumer, class Iterator, class Sentinel>
  std::pair<Iterator, ec> parse(Consumer& consumer, Iterator first,
                                Sentinel last) {
    value_type x;
    return parse(consumer, x, first, last);
  }

  template <class NewToken>
  constexpr one_or_more<Parser, NewToken> operator[](NewToken) const {
    return {p_};
  }

private:
  Parser p_;
};

template <class Parser, class Token = unit_v>
class zero_or_more : public parser_tag {
public:
  using token = Token;

  constexpr zero_or_more() {
    // nop
  }

  constexpr zero_or_more(Parser p) : p_(std::move(p)) {
    // nop
  }

  using value_token = typename Parser::token;

  using value_type = typename Parser::value_type;

  template <class Consumer, class Iterator, class Sentinel>
  std::pair<Iterator, ec> parse(Consumer& consumer, value_type& x,
                                Iterator first, Sentinel last) {
    consumer.begin_sequence(token::value);
    auto res = std::make_pair(first, ec::none);
    decltype(res) last_res;
    do {
      x = 0; // TODO: make generic
      last_res = res;
      res = p_.parse(consumer, x, res.first, last);
    } while (res.second != ec::none);
    consumer.end_sequence(token::value);
    return last_res;
  }

  template <class Consumer, class Iterator, class Sentinel>
  std::pair<Iterator, ec> parse(Consumer& consumer, Iterator first,
                                Sentinel last) {
    value_type x;
    return parse(consumer, x, first, last);
  }

  template <class NewToken>
  constexpr zero_or_more<Parser, NewToken> operator[](NewToken) const {
    return {p_};
  }

private:
  Parser p_;
};

template <class Parser0, class Parser1, class Token = unit_v>
class sequence : public parser_tag {
public:
  using token = Token;

  constexpr sequence() {
    // nop
  }

  constexpr sequence(Parser0 p0, Parser1 p1)
      : p0_(std::move(p0)),
        p1_(std::move(p1)) {
    // nop
  }

  template <class Consumer, class Iterator, class Sentinel>
  std::pair<Iterator, ec> parse(Consumer& consumer, Iterator first,
                                Sentinel last) {
    auto r0 = p0_.parse(consumer, first, last);
    if (r0.second != ec::none)
      return r0;
    return p1_.parse(consumer, r0.first, last);
  }

private:
  Parser0 p0_;
  Parser1 p1_;
};

template <class Token = unit_v>
class literal : public parser_tag {
public:
  constexpr literal(const char* cstr) : cstr_(cstr) {
    // nop
  }
  
  constexpr literal(const literal& other) : cstr_(other.cstr_) {
    // nop
  }

  template <class Consumer, class Iterator, class Sentinel>
  std::pair<Iterator, ec> parse(Consumer& consumer, Iterator first,
                                Sentinel last) const {
    auto p = std::mismatch(first, last, cstr_);
    if (*p.second == '\0') {
      consumer.constant(Token::value, cstr_);
      return {p.first, ec::none};
    }
    return {p.first, ec::invalid_character};
  }

private:
  const char* cstr_;
};

template <class Parser0, class Parser1,
          class E = detail::enable_if_t<is_parser<Parser0>::value
                                        && is_parser<Parser1>::value>>
constexpr sequence<Parser0, Parser1> operator>>(Parser0 x, Parser1 y) {
  return {std::move(x), std::move(y)};
}

template <class Parser, class E = detail::enable_if_tt<is_parser<Parser>>>
constexpr one_or_more<Parser> operator+(Parser x) {
  return {std::move(x)};
}

template <class Parser, class E = detail::enable_if_tt<is_parser<Parser>>>
constexpr zero_or_more<Parser> operator*(Parser x) {
  return {std::move(x)};
}

literal<> lit(const char* cstr) {
  return {cstr};
}

template <class Token>
literal<Token> lit(const char* cstr, Token) {
  return {cstr};
}

//static constexpr auto int64 = single<integer<int64_t>>{};

template <class Parser, class Consumer, class Iterator, class Sentinel>
bool parse(Parser p, Consumer& consumer, Iterator first, Sentinel last) {
  auto res = p.parse(consumer, first, last);
  return res.first == last && res.second == ec::none;
}

namespace {

constexpr const char single_long[] = "8943632";

using std::begin;
using std::end;

void BM_strtol(benchmark::State& state) {
  for (auto _ : state) {
    char* p;
    benchmark::DoNotOptimize(strtol(begin(single_long), &p, 10));
  }
}

void BM_caf_parse_single_long(benchmark::State& state) {
  auto f = [](const char* first, const char* last) {
    struct int_reader {
      long& n;
      inline void value(unit_t, long x) {
        n = x;
      }
    };
    long n;
    int_reader reader{n};
    single<integer<long>> p;
    p.parse(reader, first, last);
    return n;
  };
  for (auto _ : state)
    benchmark::DoNotOptimize(f(begin(single_long), end(single_long)));
}

void BM_spirit_parse_single_long(benchmark::State& state) {
  auto f = [](char const* first, char const* last) {
    namespace qi = boost::spirit::qi;
    long n;
    qi::parse(first, last, qi::long_, n);
    return n;
  };
  for (auto _ : state) {
    benchmark::DoNotOptimize(f(begin(single_long), end(single_long)));
  }
}
constexpr const char two_longs[] = "8943632 and -90823211";

template <class T>
struct wrap_v {
  static constexpr T value = T{};
};

void BM_caf_parse_two_longs(benchmark::State& state) {
  using i0 = std::integral_constant<long, 0>;
  using i1 = std::integral_constant<long, 1>;
  auto f = [](const char* first, const char* last) {
    struct reader {
      long& a;
      long& b;
      inline void value(std::integral_constant<long, 0>, long x) {
        a = x;
      }
      inline void constant(unit_t, const char*) {
        // nop
      }
      inline void value(std::integral_constant<long, 1>, long x) {
        b = x;
      }
    };
    long a;
    long b;
    reader reader{a, b};
    single<integer<long>> lval;
    auto p = lval[wrap_v<i0>{}] >> lit(" and ") >> lval[wrap_v<i1>{}];
    p.parse(reader, first, last);
    return a + b;
  };
  for (auto _ : state)
    benchmark::DoNotOptimize(f(begin(two_longs), end(two_longs)));
}

void BM_spirit_parse_two_longs(benchmark::State& state) {
  auto f = [](char const* first, char const* last) {
    namespace qi = boost::spirit::qi;
    long a;
    long b;
    auto set_a = [&](long x) { a = x; };
    auto set_b = [&](long x) { b = x; };
    qi::parse(first, last, qi::long_[set_a] >> " and " >> qi::long_[set_b]);
    return a + b;
  };
  for (auto _ : state)
    benchmark::DoNotOptimize(f(begin(two_longs), end(two_longs)));
}

} // namespace <anonymous>

BENCHMARK(BM_strtol);
BENCHMARK(BM_caf_parse_single_long);
BENCHMARK(BM_spirit_parse_single_long);
BENCHMARK(BM_caf_parse_two_longs);
BENCHMARK(BM_spirit_parse_two_longs);

BENCHMARK_MAIN();

/*
int main() {
  auto f = [](char const* first, char const* last) {
    namespace qi = boost::spirit::qi;
    long a;
    long b;
    auto set_a = [&](long x) {
      cout << "set a: " << x << endl;
      a = x;
    };
    auto set_b = [&](long x) {
      cout << "set b: " << x << endl;
      b = x;
    };
    qi::parse(first, last, qi::long_[set_a] >> " and " >> qi::long_[set_b]);
    return a + b;
  };
  f(begin(two_longs), end(two_longs));
}
// */

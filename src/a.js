const true_fn = x => y => x
const false_fn = x => y => y
const not_fn = x => x(false_fn)(true_fn)
const and_fn = x => y => x(y)(false_fn)

console.log(not_fn(true_fn))

// when calling not_fn(true_fn) this is what happens
//
// let's rewrite the function calls by swapping the parameters in
// 1. not_fn(true_fn) = true_fn => true_fn(false_fn)(true_fn)
// 2. true_fn(false_fn)(true_fn) = (false_fn => y => false_fn)(true_fn) = (y => false_fn)(true_fn)
// 3. true_fn => false_fn
// 4. false_fn

console.log(not_fn(false_fn))

// when calling not_fn(true_fn) this is what happens
//
// let's rewrite the function calls by swapping the parameters in
// 1. not_fn(false_fn) = false_fn => false_fn(false_fn)(true_fn)
// 2. false_fn(false_fn)(true_fn) = (false_fn => y => y)(true_fn) = (y => y)(true_fn)
// 3. true_fn => true_fn
// 4. true_fn

console.log(and_fn(true_fn)("u"))

// when calling and_fn(true_fn)("u") this is what happens
//
// 1. and_fn(true_fn)("u") = (true_fn => y => true_fn(y)(false_fn))("u") = (y => true_fn(y)(false_fn))("u")
// 2. "u" => true_fn("u")(false_fn)
// 3. true_fn("u")(false_fn) = ("u" => y => "u")(false_fn) = (y => "u")(false_fn)
// 4. false_fn => "u"
// 5. "u"

console.log(and_fn(false_fn)("u"))

// when calling and_fn(true_fn)("u") this is what happens
//
// 1. and_fn(false_fn)("u") = (false_fn => y => false_fn(y)(false_fn))("u") = (y => false_fn(y)(false_fn))("u")
// 2. "u" => false_fn("u")(false_fn)
// 3. false_fn("u")(false_fn) = ("u" => y => y)(false_fn) = (y => y)(false_fn)
// 4. false_fn => false_fn
// 5. false_fn

zero = s => z => z
uno = s => z => s(z)
due = s => z => s(s(z))
tre = s => z => s(s(s(z)))
succ = n => s => z => s(n(s)(z))
sum = m => n => z => s => n(z)(m(z)(s))
mul = m => n => z => s => n(m(z))(s)
toInt = n => n(x => x + 1)(0)
toChurch = i => (i === 0) ? zero : succ(toChurch(i - 1))

console.log(toInt(due))

// when calling toInt(due)
// 1. toInt(due) = due => due(x => x + 1)(0)
// 2. due(x => x + 1)(0) = (s => z => s(s(z)))(x => x + 1)(0) = (z => (x => x + 1)(x => x + 1)(z)))(0)
// 3. (z => s(s(z)))(0) dove s = (x => x + 1)
//   3a. s(s(0)) dove s = (x => x + 1)
//       (x => x + 1)((x => x + 1)(0)) = (x => x + 1)(0 + 1) = (x => (0 + 1) + 1)
//       (2)
// 4. 2

console.log(toInt(mul(due)(tre)))


//! joi - combinatory functional array programming language

#![deny(
	unreachable_patterns,
	unused_results,
	unused_variables,
)]

use std::fmt::Display;

use clap::Parser;



#[derive(Parser, Debug)]
#[clap(
	about,
	author,
	version,
	help_template = "\
		{before-help}{name} v{version}\n\
		\n\
		{about}\n\
		\n\
		Author: {author}\n\
		\n\
		{usage-heading} {usage}\n\
		\n\
		{all-args}{after-help}\
	",
)]
struct CliArgs {
	#[arg(short='d', long, default_value_t=false)]
	debug: bool,

	// TODO?
	// #[arg(short='i', long, default_value_t=false)]
	// input_at_the_end: bool,

	// TODO: execute from file by filename

	program: Vec<String>,
}



fn main() {
	let CliArgs {
		debug,
		program,
	} = CliArgs::parse();

	let result = eval_(&program.join(" "), debug);
	println!("result: {result}");
}





#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Value {
	Int(i64),
	Array(Vec<Value>),
}
impl Value {
	fn deep_apply(self, f: fn(i64) -> Value) -> Value {
		use Value::*;
		match self {
			Int(n) => f(n),
			Array(arr) => Array(
				arr.into_iter()
					.map(|el| el.deep_apply(f))
					.collect()
			)
		}
	}
}
impl From<&str> for Value {
	fn from(s: &str) -> Self {
		use Value::*;
		// dbg!(s);
		let s = s.trim();
		if s.is_empty() { return Array(vec![]) }
		if s.contains("____") {
			Array(
				s
					.split("____")
					.filter(|el| !el.is_empty())
					.map(Value::from)
					.collect()
			)
		}
		else if s.contains("__") {
			Array(
				s
					.split("__")
					// .filter(|el| !el.is_empty())
					.map(Value::from)
					.collect()
			)
		}
		else if s.contains(',') {
			Array(
				s
					.split(',')
					.filter(|el| !el.is_empty())
					.map(Value::from)
					.collect()
			)
		}
		else {
			Int(
				s
					// .trim()
					.parse()
					.unwrap()
			)
		}
	}
}
impl<const N: usize> From<[i64; N]> for Value {
	fn from(arr: [i64; N]) -> Self {
		use Value::*;
		Array(arr.map(Int).to_vec())
	}
}
impl From<Vec<i64>> for Value {
	fn from(arr: Vec<i64>) -> Self {
		use Value::*;
		Array(arr.iter().map(|n| Int(*n)).collect())
	}
}
impl<const N: usize> From<[Vec<i64>; N]> for Value {
	fn from(arr: [Vec<i64>; N]) -> Self {
		use Value::*;
		Array(arr.map(Value::from).to_vec())
	}
}
impl Display for Value {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use Value::*;
		match self {
			Int(n) => {
				write!(f, "{n}")
			}
			Array(arr) => {
				write!(f, "[")?;
				let mut it = arr.iter();
				if let Some(el) = it.next() {
					write!(f, "{el}")?;
					for el in it {
						write!(f, ", {el}")?;
					}
				}
				write!(f, "]")
			}
		}
	}
}





#[derive(Debug, Clone)]
enum Function {
	Argument,
	Literal(Value),

	Warbler(Box<[Function; 2]>),
	Cardinal(Box<[Function; 3]>),
	Starling(Box<[Function; 3]>),

	Identity(Box<Function>),
	IsEven(Box<Function>),
	IsPositive(Box<Function>),
	Negate(Box<Function>),
	Not(Box<Function>),
	Range(Box<Function>),
	Sort(Box<Function>),
	Square(Box<Function>),

	Add(Box<[Function; 2]>),
	Filter(Box<[Function; 2]>), // TODO: make two: filter-leave and filter-remove or something like that
	IsEqual(Box<[Function; 2]>),
	IsGreater(Box<[Function; 2]>),
	IsGreaterEqual(Box<[Function; 2]>),
	IsLess(Box<[Function; 2]>),
	IsLessEqual(Box<[Function; 2]>),
	IsNotEqual(Box<[Function; 2]>),
	Map(Box<[Function; 2]>),
	Reduce(Box<[Function; 2]>),
	Subtract(Box<[Function; 2]>),

	If(Box<[Function; 3]>),
}
impl Function {
	fn from_str(tokens: &str) -> Self {
		let mut tokens = tokens
			.split(' ')
			.filter(|el| !el.is_empty())
			.collect::<Vec<_>>();
		let f = Self::from_strs(&mut tokens);
		assert!(tokens.is_empty(), "NOT ALL TOKENS ARE USED!");
		f
	}

	// TODO?
	// fn arity(&self) -> u8 {
	// 	use Function::*;
	// 	match self {
	// 		| Argument
	// 		| Literal(_)
	// 		=> 0,
	// 		| Cardinal(_) // ?
	// 		=> 1,
	// 		| Warbler(_) // ???
	// 		| Starling(_) // ?
	// 		=> 2,
	// 		| Identity(_)
	// 		| Negate(_)
	// 		| Sort(_)
	// 		| Square(_)
	// 		=> 1,
	// 		| Add(_)
	// 		| Subtract(_)
	// 		=> 2,
	// 	}
	// }

	fn from_strs(tokens: &mut Vec<&str>) -> Self {
		use Function::*;
		if tokens.is_empty() { return Argument }
		macro_rules! a { () => (Box::new(Function::from_strs(tokens))) }
		macro_rules! ab { () => (Box::new([ Function::from_strs(tokens), Function::from_strs(tokens) ])) }
		macro_rules! abc { () => (Box::new([ Function::from_strs(tokens), Function::from_strs(tokens), Function::from_strs(tokens) ])) }
		match tokens.remove(0) {
			"_" => Argument,
			s if s.starts_with(['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) || s.contains(',') => Literal(Value::from(s)),

			"w" => Warbler(ab!()),
			"c" => Cardinal(abc!()),
			"s" => Starling(abc!()),

			"id" => Identity(a!()),
			"is-even" => IsEven(a!()),
			"is-pos" => IsPositive(a!()),
			"neg" => Negate(a!()),
			"not" => Not(a!()),
			"range" => Range(a!()),
			"sort" => Sort(a!()),
			"sq" => Square(a!()),

			"add" => Add(ab!()),
			"!=" => IsNotEqual(ab!()),
			"<" => IsLess(ab!()),
			"<=" => IsLessEqual(ab!()),
			"==" => IsEqual(ab!()),
			">" => IsGreater(ab!()),
			">=" => IsGreaterEqual(ab!()),
			"filter" => Filter(ab!()),
			"map" => Map(ab!()),
			"reduce" => Reduce(ab!()),
			"sub" => Subtract(ab!()),

			"if" => If(abc!()),

			t => panic!("unknown token: `{t}`")
		}
	}

	fn call(&self, mut args: Vec<Value>) -> Value {
		let result = self.call_(&mut args);
		assert!(args.is_empty(), "NOT ALL ARGS ARE USED!");
		result
	}
	fn call_(&self, args: &mut Vec<Value>) -> Value {
		use Function::*;
		use Value::*;
		match self {
			// 0
			Argument => args.remove(0),
			Literal(v) => v.clone(),

			Warbler(fx) => {
				let [f, x] = *fx.clone();
				// assert_eq!(2, a.arity(), "warbler expected function with arity=2 but it is {}", a.arity());
				let x = x.call_(args);
				f.call(vec![x.clone(), x])
			}
			Cardinal(fxy) => {
				let [f, x, y] = *fxy.clone();
				// assert_eq!(2, a.arity(), "cardinal expected function with arity=2 but it is {}", a.arity());
				let x = x.call_(args);
				let y = y.call_(args);
				f.call(vec![y, x])
			}
			Starling(fgx) => {
				let [f, g, x] = *fgx.clone();
				// assert_eq!(2, a.arity(), "starling expected first function with arity=2 but it is {}", a.arity());
				// assert_eq!(1, b.arity(), "starling expected second function with arity=1 but it is {}", b.arity());
				let x = x.call_(args);
				let gx = g.call(vec![x.clone()]);
				f.call(vec![x, gx])
			}

			// FUNCTIONS ARITY 1
			Identity(a) => {
				a.call_(args)
			}
			IsEven(a) => {
				a.call_(args).deep_apply(|n| Int((n % 2 == 0) as i64))
			}
			IsPositive(a) => {
				a.call_(args).deep_apply(|n| Int((n > 0) as i64))
			}
			Negate(a) => {
				a.call_(args).deep_apply(|n| Int(-n))
			}
			Not(a) => {
				a.call_(args).deep_apply(|b| Int(match b {
					0 => 1,
					1 => 0,
					n => panic!("cant apply boolean not on int: {n}. (expected \"boolean\" aka 0 or 1)")
				}))
			}
			Range(a) => {
				a.call_(args).deep_apply(|n| Array( (1..=n).map(Int).collect() ))
			}
			Sort(a) => {
				match a.call_(args) {
					Array(mut arr) => {
						arr.sort();
						Array(arr)
					}
					Int(_) => panic!("cant call sort on int")
				}
			}
			Square(a) => {
				match a.call_(args) {
					Int(n) => Int(n*n),
					arr @ Array(_) => arr.deep_apply(|n| Int(n*n))
				}
			}

			// FUNCTIONS ARITY 2
			Add(ab) => {
				let [a, b] = *ab.clone();
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int(a + b),
					_ => todo!()
				}
			}
			IsEqual(ab) => {
				let [a, b] = *ab.clone();
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int((a == b) as i64),
					_ => unimplemented!()
				}
			}
			IsGreater(ab) => {
				let [a, b] = *ab.clone();
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int((a > b) as i64),
					_ => unimplemented!()
				}
			}
			IsGreaterEqual(ab) => {
				let [a, b] = *ab.clone();
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int((a >= b) as i64),
					_ => unimplemented!()
				}
			}
			IsLess(ab) => {
				let [a, b] = *ab.clone();
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int((a < b) as i64),
					_ => unimplemented!()
				}
			}
			IsLessEqual(ab) => {
				let [a, b] = *ab.clone();
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int((a <= b) as i64),
					_ => unimplemented!()
				}
			}
			IsNotEqual(ab) => {
				let [a, b] = *ab.clone();
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int((a != b) as i64),
					_ => unimplemented!()
				}
			}
			Filter(fx) => {
				let [f, x] = *fx.clone();
				match x.call_(args) {
					Array(arr) => {
						Array(
							arr.into_iter()
								.filter(|el| match f.call(vec![el.clone()]) {
									Int(0) => false,
									Int(1) => true,
									n => panic!("cant filter by int: {n}. (expected \"boolean\" aka 0 or 1)")
								})
								.collect()
						)
					}
					Int(_) => panic!("cant use filter on int")
				}
			}
			Map(fx) => {
				let [f, x] = *fx.clone();
				match x.call_(args) {
					Array(arr) => {
						Array(
							arr.into_iter()
								.map(|el| f.call(vec![el]))
								.collect()
						)
					}
					Int(_) => panic!("cant use map on int")
				}
			}
			Reduce(fx) => {
				let [f, x] = *fx.clone();
				match x.call_(args) {
					Array(arr) => {
						arr.into_iter()
							.reduce(|acc, el| f.call(vec![acc, el]))
							.unwrap()
					}
					Int(_) => panic!("cant use reduce on int")
				}
			}
			Subtract(ab) => {
				let [a, b] = *ab.clone();
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int(a - b),
					_ => todo!()
				}
			}

			// FUNCTIONS ARITY 3
			If(abc) => {
				let [a, b, c] = *abc.clone();
				let cond = a.call_(args);
				match cond {
					Int(1) => {
						b.call_(args)
					}
					Int(0) => {
						c.call_(args)
					}
					_ => panic!("condition is not \"boolean\" aka 0 or 1")
				}
			}
		}
	}
}





#[allow(dead_code)] // its used for testing
fn eval(program: &str) -> Value {
	eval_(program, true)
}

fn eval_(program: &str, debug_fn_parsing: bool) -> Value {
	let tmp = program.split("::").collect::<Vec<_>>();
	let [args, fn_tokens] = tmp.as_slice() else { panic!("expected exactly one `::`") };
	let args: Vec<Value> = args
		.split(' ')
		.filter(|el| !el.is_empty())
		.map(Value::from)
		.collect();
	// dbg!(&args);
	// dbg!(fn_tokens);
	let function = Function::from_str(fn_tokens);
	if debug_fn_parsing { dbg!(&function); }
	function.call(args)
}





#[allow(non_snake_case)]
#[cfg(test)]
mod eval {
	use super::*;
	use Value::*;

	mod argument {
		use super::*;
		#[test] fn implicit() { assert_eq!(Int(2), eval("2 ::")) }
		#[test] fn explicit() { assert_eq!(Int(2), eval("2 :: _")) }
	}

	mod arr {
		use super::*;
		mod _1d {
			use super::*;
			#[test] fn _0() { assert_eq!(Array(vec![]), eval(", ::")) }
			#[test] fn _1() { assert_eq!(Value::from([4]), eval("4, ::")) }
			#[test] fn _1_() { assert_eq!(Value::from([4]), eval(",4 ::")) }
			#[test] fn _2() { assert_eq!(Value::from([4,5]), eval("4,5 ::")) }
			#[test] fn _2_() { assert_eq!(Value::from([4,5]), eval("4,5, ::")) }
			#[test] fn _3() { assert_eq!(Value::from([4,5,6]), eval("4,5,6 ::")) }
		}
		mod _2d {
			use super::*;
			#[test] fn _0_0() { assert_eq!(Value::from([vec![], vec![]]), eval("__ ::")) }
			#[test] fn _1_1() { assert_eq!(Value::from([vec![3], vec![4]]), eval("3,__4, ::")) }
			#[test] fn _2_2() { assert_eq!(Value::from([vec![3,4], vec![5,6]]), eval("3,4__5,6 ::")) }
		}
		mod _3d {
			use super::*;
			#[test] fn _2_2__2_2() { assert_eq!(Array(vec![Value::from([vec![3,4], vec![5,6]]), Value::from([vec![7,8], vec![9,0]])]), eval("3,4__5,6____7,8__9,0 ::")) }
		}
	}

	#[test] fn const_2() { assert_eq!(Int(2), eval(":: 2")) }
	#[test] fn identity() { assert_eq!(Int(2), eval("2 :: id")) }

	mod neg {
		use super::*;
		#[test] fn int() { assert_eq!(Int(-2), eval("2 :: neg")) }
		#[test] fn neg_int() { assert_eq!(Int(-(-2)), eval("2 :: neg neg")) }
		#[test] fn array() { assert_eq!(Value::from([-1,-2,-3]), eval("1,2,3 :: neg")) }
	}

	#[test] fn square() { assert_eq!(Int(3*3), eval("3 :: sq")) }
	#[test] fn square_arr() { assert_eq!(Value::from([1,4,9]), eval("1,2,3 :: sq")) }

	mod add {
		use super::*;
		#[test] fn int_int() { assert_eq!(Int(2+2), eval("2 2 :: add")) }
		#[test] fn arr_int() { assert_eq!(Int(2+2), eval("2 2 :: add")) }
	}

	#[test] fn sub_int_int() { assert_eq!(Int(2-3), eval("2 3 :: sub")) }
	#[test] fn neg_add() { assert_eq!(Int(-(2+2)), eval("2 2 :: neg add")) }
	#[test] fn add_neg_arg_neg() { assert_eq!(Int(-2-3), eval("2 3 :: add neg _ neg")) }

	mod warbler {
		use super::*;
		#[test] fn w_add() { assert_eq!(Int(2+2), eval("2 :: w add")) }
	}

	mod cardinal {
		use super::*;
		#[test] fn sub() { assert_eq!(Int(3-2), eval("2 3 :: c sub")) }
	}

	mod starling {
		use super::*;
		#[test] fn sub_arg_arg_sq() { assert_eq!(Int(3 - 3*3), eval("3 :: s sub _ _ sq")) }
	}

	mod sort {
		use super::*;
		#[test] fn arr() { assert_eq!(Value::from([1,2,3,4,5]), eval("4,5,2,3,1 :: sort")) }
		#[test] fn arr_of_arr() { assert_eq!(Array(vec![Int(1), Int(9), Array(vec![]), Value::from([2]), Value::from([2,3,1]), Value::from([8])]), eval("__,2__2,3,1__8,__9__1 :: sort")) }
	}

	mod range {
		use super::*;
		#[test] fn int() { assert_eq!(Value::from([1,2,3,4]), eval("4 :: range")) }
		#[test] fn arr() { assert_eq!(Value::from([vec![1,2,3], vec![1,2,3,4]]), eval("3,4 :: range")) }
	}

	mod map {
		use super::*;
		#[test]
		fn sort() {
			assert_eq!(
				Value::from([vec![1,2,3,4], vec![1,2,3,4,5]]),
				eval("3,1,4,2__4,5,1,3,2 :: map sort")
			)
		}
		#[test]
		fn add1() {
			assert_eq!(
				Value::from([2,3,4]),
				eval("1,2,3 :: map add 1")
			)
		}
	}

	mod filter {
		use super::*;
		#[test] fn is_even() { assert_eq!(Value::from([2,4,6,8]), eval("1,2,3,4,5,6,7,8,9 :: filter is-even")) }
		#[test] fn not_is_even() { assert_eq!(Value::from([1,3,5,7,9]), eval("1,2,3,4,5,6,7,8,9 :: filter not is-even")) }
		#[test] fn is_positive() { assert_eq!(Value::from([1,2]), eval("-2,-1,0,1,2 :: filter is-pos")) }
		#[test] fn not_is_positive() { assert_eq!(Value::from([-2,-1,0]), eval("-2,-1,0,1,2 :: filter not is-pos")) }
		#[test] fn is_even_via_range() { assert_eq!(Value::from([2,4,6,8]), eval("9 :: filter is-even _ range")) }
	}

	mod reduce {
		use super::*;
		#[test] fn add_aka_sum() { assert_eq!(Int(10), eval("1,2,3,4 :: reduce add")) }
		#[test] fn add_aka_sum_via_range() { assert_eq!(Int(10), eval("4 :: reduce add _ _ range")) }
	}

	mod if_ {
		use super::*;
		#[test] fn _100__is_even__add_10__sub_10() { assert_eq!(Int(100+10), eval("42 100 :: if is-even _ add 10 _ sub _ 10")) }
		#[test] fn _101__is_even__add_10__sub_10() { assert_eq!(Int(100-10), eval("43 100 :: if is-even _ add 10 _ sub _ 10")) }
		#[test] fn _100__w_is_even__add_10__sub_10() { assert_eq!(Int(100+10), eval("100 :: w if is-even _ add 10 _ sub _ 10")) }
		#[test] fn _101__w_is_even__add_10__sub_10() { assert_eq!(Int(101-10), eval("101 :: w if is-even _ add 10 _ sub _ 10")) }
	}

	mod is_equal {
		use super::*;
		#[test] fn _10_10() { assert_eq!(Int(1), eval("10 10 :: ==")) }
		#[test] fn _10_99() { assert_eq!(Int(0), eval("10 99 :: ==")) }
		#[test] fn _99_10() { assert_eq!(Int(0), eval("99 10 :: ==")) }
	}
	mod is_greater {
		use super::*;
		#[test] fn _10_10() { assert_eq!(Int(0), eval("10 10 :: >")) }
		#[test] fn _10_99() { assert_eq!(Int(0), eval("10 99 :: >")) }
		#[test] fn _99_10() { assert_eq!(Int(1), eval("99 10 :: >")) }
	}
	mod is_greater_equal {
		use super::*;
		#[test] fn _10_10() { assert_eq!(Int(1), eval("10 10 :: >=")) }
		#[test] fn _10_99() { assert_eq!(Int(0), eval("10 99 :: >=")) }
		#[test] fn _99_10() { assert_eq!(Int(1), eval("99 10 :: >=")) }
	}
	mod is_less {
		use super::*;
		#[test] fn _10_10() { assert_eq!(Int(0), eval("10 10 :: <")) }
		#[test] fn _10_99() { assert_eq!(Int(1), eval("10 99 :: <")) }
		#[test] fn _99_10() { assert_eq!(Int(0), eval("99 10 :: <")) }
	}
	mod is_less_equal {
		use super::*;
		#[test] fn _10_10() { assert_eq!(Int(1), eval("10 10 :: <=")) }
		#[test] fn _10_99() { assert_eq!(Int(1), eval("10 99 :: <=")) }
		#[test] fn _99_10() { assert_eq!(Int(0), eval("99 10 :: <=")) }
	}
	mod is_not_equal {
		use super::*;
		#[test] fn _10_10() { assert_eq!(Int(0), eval("10 10 :: !=")) }
		#[test] fn _10_99() { assert_eq!(Int(1), eval("10 99 :: !=")) }
		#[test] fn _99_10() { assert_eq!(Int(1), eval("99 10 :: !=")) }
	}

	#[test] fn _10__w_if_equal_10__sq__neg() { assert_eq!(Int(100), eval("10 :: w if == 10 _ sq _ neg")) }
	#[test] fn _11__w_if_equal_10__sq__neg() { assert_eq!(Int(-11), eval("11 :: w if == 10 _ sq _ neg")) }
}


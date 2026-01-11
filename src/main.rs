//! joi - combinatory functional array programming language

#![deny(
	unreachable_patterns,
	unused_results,
	unused_variables,
)]

use std::fmt::Display;

use clap::Parser;

mod lib_;
use crate::lib_::*;





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
	// #[arg(short='D', long, default_value_t=false)]
	// debug_parsing: bool,
	//
	// #[arg(short='d', long, default_value_t=false)]
	// debug_eval: bool,

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
		// debug_parsing,
		// debug_eval,
		debug,
		program,
	} = CliArgs::parse();

	// let result = eval_(&program.join(" "), debug_parsing, debug_eval);
	let result = eval_(&program.join(" "), debug, debug);
	println!("result: {result}");
}





#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Value {
	Int(i64),
	// TODO: rename into List?
	Array(Vec<Value>),
}
impl Value {
	fn deep_map(self, f: fn(i64) -> Self) -> Self {
		use Value::*;
		match self {
			Int(n) => f(n),
			Array(arr) => Array(
				arr.into_iter()
					.map(|el| el.deep_map(f))
					.collect()
			)
		}
	}
	fn try_as_int(self) -> Option<i64> {
		use Value::*;
		match self {
			Int(n) => Some(n),
			Array(_) => None,
		}
	}
	fn try_as_ints(self) -> Option<Vec<i64>> {
		use Value::*;
		let Array(arr) = self else { return None };
		Some(
			arr.into_iter()
				.map(|v| v.try_as_int().unwrap())
				.collect()
		)
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
// impl From<&[i64]> for Value {
// 	fn from(arr: &[i64]) -> Self {
// 		use Value::*;
// 		Array(arr.iter().map(|n| Int(*n)).collect())
// 	}
// }
// impl<const N: usize> From<[&[i64]; N]> for Value {
// 	fn from(arr: [&[i64]; N]) -> Self {
// 		use Value::*;
// 		// Array(arr.map(Value::from).to_vec())
// 		Array(arr.map(|s| Value::from(s.to_vec())).to_vec()) // better?
// 	}
// }
impl<const N: usize, const M: usize> From<[[i64; M]; N]> for Value {
	fn from(arr: [[i64; M]; N]) -> Self {
		use Value::*;
		Array(arr.map(Value::from).to_vec())
	}
}
impl<const N: usize, const M: usize, const K: usize> From<[[[i64; K]; M]; N]> for Value {
	fn from(arr: [[[i64; K]; M]; N]) -> Self {
		use Value::*;
		Array(arr.map(Value::from).to_vec())
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

	// BIRDS:
	// src: combinatorylogic.com/table.html
	Warbler(Box<[Function; 2]>), // W = f,x -> f(x,x)
	Cardinal(Box<[Function; 3]>), // C = f,x,y -> f(y,x)
	// Bluebird // B = f,g,x -> f(g(x))
	// Blackbird // B1 = f,g,x,y -> f(g(x,y))
	// Bunting // B2 = f,g,x,y,z -> f(g(x,y,z))
	// Becard // B3? = f,g,h,x -> f(g(h(x)))
	Starling(Box<[Function; 3]>), // S = f,g,x -> f(x, g(x))
	Starling1(Box<[Function; 4]>), // S' = f,g,x,y -> f(x, g(x,y))
	VioletStarling(Box<[Function; 3]>), // Sigma = f,g,x -> f(g(x), x)
	// Dove // D = f,g,x,y -> f(x, g(y))
	// ZebraDove // Delta = f,g,x,y -> f(g(x), y)
	Phoenix(Box<[Function; 4]>), // Phi = f,g,h,x -> f(g(x), h(x))
	// Psi = f,g,x,y -> f(g(x), g(y))
	// Dickcissel // D1 = f,g,x,y,z -> f(x, y, g(z))
	// Dovekie // D2 = f,g,h,x,y -> f(g(x), h(y))
	// Eagle // E = f,g,h,x,y -> f(x, g(y,z))
	// GoldenEagle // epsilon = f,g,h,x,y -> f(g(x,y), z)
	// Pheasant // Phi1 = f,g,h,x,y -> f(g(x,y), h(x,y))
	// BaldEagle // hatE = f,g,h,x,y,z,t -> f(g(x,y),h(z,t))

	Absolute(Box<Function>),
	CoDedup(Box<Function>),
	// CubeRoot(Box<Function>),
	Dedup(Box<Function>),
	// Decrease(Box<Function>),
	First(Box<Function>),
	Head(Box<Function>), // everything but last
	Identity(Box<Function>),
	// Increase(Box<Function>),
	IndexOfMaxFirst(Box<Function>),
	IndexOfMaxLast(Box<Function>),
	IndexOfMinFirst(Box<Function>),
	IndexOfMinLast(Box<Function>),
	IsEven(Box<Function>),
	// IsOdd(Box<Function>),
	IsPositive(Box<Function>),
	// IsNegative(Box<Function>),
	// IsZero(Box<Function>),
	Last(Box<Function>),
	Max(Box<Function>),
	Min(Box<Function>),
	Negate(Box<Function>),
	Not(Box<Function>),
	// Product(Box<Function>),
	Range(Box<Function>),
	Reverse(Box<Function>),
	Sort(Box<Function>),
	Square(Box<Function>),
	SquareRoot(Box<Function>),
	Sum(Box<Function>),
	Tail(Box<Function>), // everything but first
	Transpose(Box<Function>),

	Add(Box<[Function; 2]>),
	At(Box<[Function; 2]>),
	Chunks(Box<[Function; 2]>),
	CoDedupBy(Box<[Function; 2]>),
	DedupBy(Box<[Function; 2]>),
	// Divide(Box<[Function; 2]>),
	Drop(Box<[Function; 2]>), // drop n first from array
	Filter(Box<[Function; 2]>), // TODO: make two: filter-leave and filter-remove or something like that
	// Find(Box<[Function; 2]>),
	// IndexOf/Position
	// Insert(Box<[Function; 2]>),
	IsEqual(Box<[Function; 2]>),
	IsGreater(Box<[Function; 2]>),
	IsGreaterEqual(Box<[Function; 2]>),
	IsLess(Box<[Function; 2]>),
	IsLessEqual(Box<[Function; 2]>),
	IsNotEqual(Box<[Function; 2]>),
	Join(Box<[Function; 2]>),
	Map(Box<[Function; 2]>),
	Max2(Box<[Function; 2]>),
	Min2(Box<[Function; 2]>),
	Modulo(Box<[Function; 2]>),
	ModuloFake(Box<[Function; 2]>),
	// Multiply(Box<[Function; 2]>),
	Reduce(Box<[Function; 2]>),
	// Rotate(Box<[Function; 2]>),
	Running(Box<[Function; 2]>), // like running sum, `running_max`
	Running2(Box<[Function; 2]>), // like running sum, `running_max`
	Subtract(Box<[Function; 2]>),
	Take(Box<[Function; 2]>), // take n first from array
	Windows(Box<[Function; 2]>),
	Zip(Box<[Function; 2]>),

	// Slice
	// SplitAtIndex/Function

	// Fold(Box<[Function; 3]>),
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

	fn from_strs(tokens: &mut Vec<&str>) -> Self {
		use Function::*;
		if tokens.is_empty() { return Argument }
		macro_rules! a { () => (Box::new(Function::from_strs(tokens))) }
		macro_rules! ab { () => (Box::new([ Function::from_strs(tokens), Function::from_strs(tokens) ])) }
		macro_rules! abc { () => (Box::new([ Function::from_strs(tokens), Function::from_strs(tokens), Function::from_strs(tokens) ])) }
		macro_rules! abcd { () => (Box::new([ Function::from_strs(tokens), Function::from_strs(tokens), Function::from_strs(tokens), Function::from_strs(tokens) ])) }
		match tokens.remove(0) {
			"_" => Argument,
			// TODO: _2 -> _ _ , _3 -> _ _ _ , ...
			s if s.starts_with(['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) || s.contains(',') => Literal(Value::from(s)),

			"w" => Warbler(ab!()),
			"c" => Cardinal(abc!()),
			"s" => Starling(abc!()),
			"s1" => Starling1(abcd!()),
			"sigma" => VioletStarling(abc!()),
			"phi" => Phoenix(abcd!()),

			"abs" => Absolute(a!()),
			"codedup" => CoDedup(a!()),
			"dedup" => Dedup(a!()),
			"first" => First(a!()),
			"head" => Head(a!()),
			"id" => Identity(a!()),
			"imaxf" => IndexOfMaxFirst(a!()),
			"imaxl" => IndexOfMaxLast(a!()),
			"iminf" => IndexOfMinFirst(a!()),
			"iminl" => IndexOfMinLast(a!()),
			"is-even" => IsEven(a!()),
			"is-pos" => IsPositive(a!()),
			"last" => Last(a!()),
			"max" => Max(a!()),
			"min" => Min(a!()),
			"neg" => Negate(a!()),
			"not" => Not(a!()),
			"range" => Range(a!()),
			"rev" => Reverse(a!()),
			"sort" => Sort(a!()),
			"sq" => Square(a!()),
			"sqrt" => SquareRoot(a!()),
			"sum" => Sum(a!()),
			"tail" => Tail(a!()),
			"transpose" => Transpose(a!()),

			"add" => Add(ab!()),
			"at" => At(ab!()),
			"chunks" => Chunks(ab!()),
			"codedup-by" => CoDedupBy(ab!()),
			"dedup-by" => DedupBy(ab!()),
			"drop" => Drop(ab!()),
			"!=" => IsNotEqual(ab!()),
			"<" => IsLess(ab!()),
			"<=" => IsLessEqual(ab!()),
			"==" => IsEqual(ab!()),
			">" => IsGreater(ab!()),
			">=" => IsGreaterEqual(ab!()),
			"filter" => Filter(ab!()),
			"join" => Join(ab!()),
			"map" => Map(ab!()),
			"max2" => Max2(ab!()),
			"min2" => Min2(ab!()),
			"mod" => Modulo(ab!()),
			"modf" => ModuloFake(ab!()),
			"reduce" => Reduce(ab!()),
			"running" => Running(ab!()),
			"running2" => Running2(ab!()),
			"sub" => Subtract(ab!()),
			"take" => Take(ab!()),
			"windows" => Windows(ab!()),
			"zip" => Zip(ab!()),

			"if" => If(abc!()),

			t => panic!("unknown token: `{t}`")
		}
	}

	fn eval(&self, mut args: Vec<Value>) -> Value {
		let result = self.eval_(&mut args);
		assert!(args.is_empty(), "NOT ALL ARGS ARE USED!");
		result
	}
	fn eval_(&self, args: &mut Vec<Value>) -> Value {
		// TODO(bench): `&self` vs `self`.
		use Function::*;
		use Value::*;
		let res = match self {
			// 0
			Argument => args.remove(0),
			Literal(v) => v.clone(),

			Warbler(fx) => {
				let [f, x] = *fx.clone();
				// assert_eq!(2, a.arity(), "warbler expected function with arity=2 but it is {}", a.arity());
				let x = x.eval_(args);
				f.eval(vec![x.clone(), x])
			}
			Cardinal(fxy) => {
				let [f, x, y] = *fxy.clone();
				// assert_eq!(2, a.arity(), "cardinal expected function with arity=2 but it is {}", a.arity());
				let x = x.eval_(args);
				let y = y.eval_(args);
				f.eval(vec![y, x])
			}
			Starling(fgx) => {
				let [f, g, x] = *fgx.clone();
				// assert_eq!(2, a.arity(), "starling expected first function with arity=2 but it is {}", a.arity());
				// assert_eq!(1, b.arity(), "starling expected second function with arity=1 but it is {}", b.arity());
				let x = x.eval_(args);
				let gx = g.eval(vec![x.clone()]);
				f.eval(vec![x, gx])
			}
			Starling1(fgxy) => {
				let [f, g, x, y] = *fgxy.clone();
				let x = x.eval_(args);
				let y = y.eval_(args);
				let gxy = g.eval(vec![x.clone(), y]);
				f.eval(vec![x, gxy])
			}
			VioletStarling(fgx) => {
				let [f, g, x] = *fgx.clone();
				let x = x.eval_(args);
				let gx = g.eval(vec![x.clone()]);
				f.eval(vec![gx, x])
			}
			Phoenix(fghx) => {
				let [f, g, h, x] = *fghx.clone();
				let x = x.eval_(args);
				let gx = g.eval(vec![x.clone()]);
				let hx = h.eval(vec![x]);
				f.eval(vec![gx, hx])
			}

			// FUNCTIONS ARITY 1
			Absolute(a) => {
				a.eval_(args).deep_map(|n| Int(n.abs()))
			}
			CoDedup(a) => {
				match a.eval_(args) {
					Array(arr) => {
						Array(arr.codedup())
					}
					_ => panic!("codedup: expected array")
				}
			}
			Dedup(a) => {
				match a.eval_(args) {
					Array(mut arr) => {
						arr.dedup();
						Array(arr)
					}
					_ => panic!("dedup: expected array")
				}
			}
			First(a) => {
				match a.eval_(args) {
					Array(mut arr) => arr.remove(0),
					_ => panic!("first: expected array")
				}
			}
			Head(a) => {
				match a.eval_(args) {
					Array(arr) => Array(arr[..arr.len()-1].to_vec()),
					_ => panic!("head: expected array")
				}
			}
			Identity(a) => {
				a.eval_(args)
			}
			IndexOfMaxFirst(a) => {
				match a.eval_(args) {
					arr @ Array(_) => {
						let Some(arr) = arr.try_as_ints() else { panic!("imaxf: expected flat array of ints") };
						Int(arr.index_of_max_first() as i64)
					}
					_ => panic!("imaxf: expected array")
				}
			}
			IndexOfMaxLast(a) => {
				match a.eval_(args) {
					arr @ Array(_) => {
						let Some(arr) = arr.try_as_ints() else { panic!("imaxl: expected flat array of ints") };
						Int(arr.index_of_max_last() as i64)
					}
					_ => panic!("imaxl: expected array")
				}
			}
			IndexOfMinFirst(a) => {
				match a.eval_(args) {
					arr @ Array(_) => {
						let Some(arr) = arr.try_as_ints() else { panic!("iminf: expected flat array of ints") };
						Int(arr.index_of_min_first() as i64)
					}
					_ => panic!("iminf: expected array")
				}
			}
			IndexOfMinLast(a) => {
				match a.eval_(args) {
					arr @ Array(_) => {
						let Some(arr) = arr.try_as_ints() else { panic!("iminl: expected flat array of ints") };
						Int(arr.index_of_min_last() as i64)
					}
					_ => panic!("iminl: expected array")
				}
			}
			IsEven(a) => {
				a.eval_(args).deep_map(|n| Int((n % 2 == 0) as i64))
			}
			IsPositive(a) => {
				a.eval_(args).deep_map(|n| Int((n > 0) as i64))
			}
			Last(a) => {
				match a.eval_(args) {
					Array(mut arr) => arr.remove(arr.len()-1),
					_ => panic!("last: expected array")
				}
			}
			Max(a) => {
				match a.eval_(args) {
					arr @ Array(_) => Int(arr.try_as_ints().unwrap().into_iter().max().unwrap()),
					_ => panic!("max: expected array")
				}
			}
			Min(a) => {
				match a.eval_(args) {
					arr @ Array(_) => Int(arr.try_as_ints().unwrap().into_iter().min().unwrap()),
					_ => panic!("min: expected array")
				}
			}
			Negate(a) => {
				a.eval_(args).deep_map(|n| Int(-n))
			}
			Not(a) => {
				a.eval_(args).deep_map(|b| Int(match b {
					0 => 1,
					1 => 0,
					n => panic!("not: cant apply on int: {n}. (expected \"boolean\" aka 0 or 1)")
				}))
			}
			Range(a) => {
				a.eval_(args).deep_map(|n| Array( (1..=n).map(Int).collect() ))
			}
			Reverse(a) => {
				match a.eval_(args) {
					Array(mut arr) => Array({ arr.reverse(); arr }),
					_ => panic!("rev: expected array")
				}
			}
			Sort(a) => {
				match a.eval_(args) {
					Array(mut arr) => {
						arr.sort();
						Array(arr)
					}
					Int(_) => panic!("sort: cant call on int")
				}
			}
			Square(a) => {
				match a.eval_(args) {
					Int(n) => Int(n*n),
					arr @ Array(_) => arr.deep_map(|n| Int(n*n))
				}
			}
			SquareRoot(a) => {
				a.eval_(args).deep_map(|n| Int(n.isqrt()))
			}
			Sum(a) => {
				match a.eval_(args) {
					Array(arr) => Int(
						arr.into_iter()
							.fold(0, |acc, el| {
								match el {
									Int(el) => acc + el,
									_ => panic!("sum: cant add not int")
								}
							})
					),
					_ => panic!("sum: cant sum not array")
				}
			}
			Tail(a) => {
				match a.eval_(args) {
					Array(arr) => Array(arr[1..].to_vec()),
					_ => panic!("tail: expected array")
				}
			}
			Transpose(a) => {
				match a.eval_(args) {
					Array(arr) => Array(
						transpose(arr.into_iter().map(|arr| match arr {
							Array(arr) => arr,
							_ => panic!("transpose: expected array of arrays")
						}).collect())
						.into_iter().map(Array).collect()
					),
					_ => panic!("transpose: cant call on not array")
				}
			}

			// FUNCTIONS ARITY 2
			Add(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int(a + b),
					(arr @ Array(_), Int(n)) | (Int(n), arr @ Array(_)) => {
						let Some(arr) = arr.try_as_ints() else { panic!("add: expected flat array of ints") };
						let res = arr.into_iter().map(|a| Int(a + n)).collect();
						Array(res)
					}
					(a @ Array(_), b @ Array(_)) => {
						let Some(a) = a.try_as_ints() else { panic!("add: expected flat array of ints as first arg") };
						let Some(b) = b.try_as_ints() else { panic!("add: expected flat array of ints as second arg") };
						assert_eq!(a.len(), b.len(), "add: expected arrays to have same length");
						let res = a.into_iter().zip(b).map(|(a, b)| Int(a + b)).collect();
						Array(res)
					}
				}
			}
			At(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(_a), Int(_b)) => panic!("at: cant index into int"),
					(Array(arr), Int(i)) => arr[usize::try_from(i).unwrap()].clone(),
					// (Int(i), Array(arr)) => arr[usize::try_from(i).unwrap()].clone(), // TODO: enable?
					(Array(arr), Array(i)) => Array(i.iter().map(|i| match i {
						Int(i) => arr[usize::try_from(*i).unwrap()].clone(),
						_ => panic!("at: cant index array by array in array")
					}).collect()),
					_ => panic!("at: wrong args order")
				}
			}
			Chunks(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(n), Array(arr)) => Array(
						arr
							.chunks(n.try_into().unwrap())
							.map(|c| Array(c.to_vec()))
							.collect()
					),
					_ => panic!("chunks: expected int and array")
				}
			}
			CoDedupBy(fx) => {
				let [f, x] = *fx.clone();
				match x.eval_(args) {
					Array(arr) => {
						Array(arr.codedup_by(|a, b| match f.eval(vec![a.clone(), b.clone()]) {
							Int(0) => false,
							Int(1) => true,
							_ => panic!("codedup-by: expected \"boolean\" aka 0 or 1 as a result of a comparison")
						}))
					}
					_ => panic!("codedup-by: expected array as second arg")
				}
			}
			DedupBy(fx) => {
				let [f, x] = *fx.clone();
				match x.eval_(args) {
					Array(mut arr) => {
						arr.dedup_by(|a, b| match f.eval(vec![a.clone(), b.clone()]) {
							Int(0) => false,
							Int(1) => true,
							_ => panic!("dedup-by: expected \"boolean\" aka 0 or 1 as a result of a comparison")
						});
						Array(arr)
					}
					_ => panic!("dedup-by: expected array as second arg")
				}
			}
			Drop(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Array(arr), Int(n)) | (Int(n), Array(arr)) => {
						Array(arr[n.try_into().unwrap()..].to_vec())
					}
					_ => panic!("drop: expected int and array")
				}
			}
			IsEqual(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int((a == b) as i64),
					_ => unimplemented!()
				}
			}
			IsGreater(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int((a > b) as i64),
					_ => unimplemented!()
				}
			}
			IsGreaterEqual(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int((a >= b) as i64),
					_ => unimplemented!()
				}
			}
			IsLess(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int((a < b) as i64),
					_ => unimplemented!()
				}
			}
			IsLessEqual(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int((a <= b) as i64),
					_ => unimplemented!()
				}
			}
			IsNotEqual(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int((a != b) as i64),
					_ => unimplemented!()
				}
			}
			Filter(fx) => {
				let [f, x] = *fx.clone();
				match x.eval_(args) {
					Array(arr) => {
						Array(
							arr.into_iter()
								.filter(|el| match f.eval(vec![el.clone()]) {
									Int(0) => false,
									Int(1) => true,
									n => panic!("filter: cant filter by int: {n}. (expected \"boolean\" aka 0 or 1)")
								})
								.collect()
						)
					}
					Int(_) => panic!("filter: cant use on int")
				}
			}
			Join(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Array(vec![Int(a), Int(b)]),
					(a @ Int(_), Array(mut b)) => Array({ b.insert(0, a); b }),
					(Array(mut a), b @ Int(_)) => Array({ a.push(b); a }),
					(Array(mut a), Array(b)) => Array({ a.extend(b); a }),
				}
			}
			Map(fx) => {
				let [f, x] = *fx.clone();
				match x.eval_(args) {
					Array(arr) => {
						Array(
							arr.into_iter()
								.map(|el| f.eval(vec![el]))
								.collect()
						)
					}
					Int(_) => panic!("map: cant use on int")
				}
			}
			Max2(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int(a.max(b)),
					(arr @ Array(_), Int(n)) | (Int(n), arr @ Array(_)) => {
						let Some(arr) = arr.try_as_ints() else { panic!("max2: expected flat array of ints as one of the args") };
						let arr_max = *arr.iter().max().unwrap();
						Int(arr_max.max(n))
					}
					(a @ Array(_), b @ Array(_)) => {
						let Some(a) = a.try_as_ints() else { panic!("max2: expected flat array of ints as first arg") };
						let Some(b) = b.try_as_ints() else { panic!("max2: expected flat array of ints as second arg") };
						let a_max = *a.iter().max().unwrap();
						let b_max = *b.iter().max().unwrap();
						Int(a_max.max(b_max))
					}
				}
			}
			Min2(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int(a.min(b)),
					(arr @ Array(_), Int(n)) | (Int(n), arr @ Array(_)) => {
						let Some(arr) = arr.try_as_ints() else { panic!("min2: expected flat array of ints as one of the args") };
						let arr_min = *arr.iter().min().unwrap();
						Int(arr_min.min(n))
					}
					(a @ Array(_), b @ Array(_)) => {
						let Some(a) = a.try_as_ints() else { panic!("min2: expected flat array of ints as first arg") };
						let Some(b) = b.try_as_ints() else { panic!("min2: expected flat array of ints as second arg") };
						let a_min = *a.iter().min().unwrap();
						let b_min = *b.iter().min().unwrap();
						Int(a_min.min(b_min))
					}
				}
			}
			Modulo(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int(a.rem_euclid(b)),
					_ => panic!("mod: expected int and int")
				}
			}
			ModuloFake(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int(a % b),
					_ => panic!("modf: expected int and int")
				}
			}
			Reduce(fx) => {
				let [f, x] = *fx.clone();
				match x.eval_(args) {
					Array(arr) => {
						arr.into_iter()
							.reduce(|acc, el| f.eval(vec![acc, el]))
							.unwrap()
					}
					Int(_) => panic!("reduce: cant use on int")
				}
			}
			Running(fx) => {
				let [f, x] = *fx.clone();
				match x.eval_(args) {
					Array(arr) => Array(
						arr.into_iter().fold(vec![], |mut acc, el| {
							if acc.is_empty() {
								vec![el]
							} else {
								let mut acc_to_eval = acc.clone();
								acc_to_eval.push(el);
								let new = f.eval(vec![Array(acc_to_eval)]);
								acc.push(new);
								acc
							}
						})
					),
					Int(_) => panic!("running: cant use on int")
				}
			}
			Running2(fx) => {
				let [f, x] = *fx.clone();
				match x.eval_(args) {
					Array(arr) => Array(
						arr.into_iter().fold(vec![], |mut acc, el| {
							if acc.is_empty() {
								vec![el]
							} else {
								let new = f.eval(vec![acc.last().unwrap().clone(), el]);
								acc.push(new);
								acc
							}
						})
					),
					Int(_) => panic!("running2: cant use on int")
				}
			}
			Subtract(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(a), Int(b)) => Int(a - b),
					(arr @ Array(_), Int(n)) => {
						let Some(arr) = arr.try_as_ints() else { panic!("sub: expected flat array of ints") };
						let res = arr.into_iter().map(|a| Int(a - n)).collect();
						Array(res)
					}
					(Int(n), arr @ Array(_)) => {
						let Some(arr) = arr.try_as_ints() else { panic!("sub: expected flat array of ints") };
						let res = arr.into_iter().map(|a| Int(n - a)).collect();
						Array(res)
					}
					(a @ Array(_), b @ Array(_)) => {
						let Some(a) = a.try_as_ints() else { panic!("sub: expected flat array of ints as first arg") };
						let Some(b) = b.try_as_ints() else { panic!("sub: expected flat array of ints as second arg") };
						assert_eq!(a.len(), b.len(), "sub: expected arrays to have same length");
						let res = a.into_iter().zip(b).map(|(a, b)| Int(a - b)).collect();
						Array(res)
					}
				}
			}
			Take(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Array(arr), Int(n)) | (Int(n), Array(arr)) => {
						Array(arr[..n.try_into().unwrap()].to_vec())
					}
					_ => panic!("drop: expected int and array")
				}
			}
			Windows(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Int(n), Array(arr)) => Array(
						arr
							.windows(n.try_into().unwrap())
							.map(|c| Array(c.to_vec()))
							.collect()
					),
					_ => panic!("windows: expected int and array")
				}
			}
			Zip(ab) => {
				let [a, b] = *ab.clone();
				match (a.eval_(args), b.eval_(args)) {
					(Array(a), Array(b)) => Array(
						a.into_iter().zip(b)
							.map(|(a, b)| Array(vec![a, b]))
							.collect()
					),
					_ => panic!("zip: expected two arrays")
				}
			}

			// FUNCTIONS ARITY 3
			If(abc) => {
				let [a, b, c] = *abc.clone();
				let cond = a.eval_(args);
				match cond {
					Int(1) => {
						b.eval_(args)
					}
					Int(0) => {
						c.eval_(args)
					}
					_ => panic!("if: condition is not \"boolean\" aka 0 or 1")
				}
			}
		};
		if true {
			eprintln!("{self:?}: {res}");
		}
		res
	}
}





#[allow(dead_code)] // its used for testing
fn eval(program: &str) -> Value {
	eval_(program, true, true)
}

fn eval_(program: &str, debug_parsing: bool, _debug_eval: bool) -> Value {
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
	if debug_parsing { dbg!(&function); }
	// dbg!(debug_eval); // TODO: FIXME
	function.eval(args)
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
			#[test] fn _0_0() { assert_eq!(Value::from([vec![],vec![]]), eval("__ ::")) }
			#[test] fn _1_1() { assert_eq!(Value::from([[3],[4]]), eval("3,__4, ::")) }
			#[test] fn _2_2() { assert_eq!(Value::from([[3,4],[5,6]]), eval("3,4__5,6 ::")) }
		}
		mod _3d {
			use super::*;
			#[test] fn _2_2__2_2() { assert_eq!(Value::from([[[3,4],[5,6]],[[7,8],[9,0]]]), eval("3,4__5,6____7,8__9,0 ::")) }
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
		#[test] fn int_int() { assert_eq!(Int(2+3), eval("2 3 :: add")) }
		#[test] fn arr_int() { assert_eq!(Value::from([3,4,5]), eval("1,2,3 2 :: add")) }
		#[test] fn int_arr() { assert_eq!(Value::from([3,4,5]), eval("2 1,2,3 :: add")) }
		#[test] fn arr_arr() { assert_eq!(Value::from([5,7,9]), eval("1,2,3 4,5,6 :: add")) }
	}
	mod sub {
		use super::*;
		#[test] fn int_int() { assert_eq!(Int(2-3), eval("2 3 :: sub")) }
		#[test] fn arr_int() { assert_eq!(Value::from([-1,0,1]), eval("1,2,3 2 :: sub")) }
		#[test] fn int_arr() { assert_eq!(Value::from([1,0,-1]), eval("2 1,2,3 :: sub")) }
		#[test] fn arr_arr() { assert_eq!(Value::from([3,4,5]), eval("4,6,8 1,2,3 :: sub")) }
	}

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
		#[test] fn running_max() { assert_eq!(Value::from([0,1,1,2,2,2,2,3,3,3]), eval("0,1,0,2,1,0,1,3,0,1 :: reduce s1 join _ _ max2")) }
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

	mod at {
		use super::*;
		#[test] fn arr_int() { assert_eq!(Int(8), eval("9,8,7,6,5 1 :: at")) }
		#[test] fn arr_arr() { assert_eq!(Value::from([8,6]), eval("9,8,7,6,5 1,3 :: at")) }
	}

	mod sqrt {
		use super::*;
		#[test] fn _0() { assert_eq!(Int(0), eval("0 :: sqrt")) }
		#[test] fn _1() { assert_eq!(Int(1), eval("1 :: sqrt")) }
		#[test] fn _4() { assert_eq!(Int(2), eval("4 :: sqrt")) }
		#[test] fn _9() { assert_eq!(Int(3), eval("9 :: sqrt")) }
		#[test] fn _16() { assert_eq!(Int(4), eval("16 :: sqrt")) }
	}

	mod sum {
		use super::*;
		#[test] fn _1_2_3() { assert_eq!(Int(6), eval("1,2,3 :: sum")) }
		#[test] fn _1_2_3_4() { assert_eq!(Int(10), eval("1,2,3,4 :: sum")) }
		#[test] fn _1_2_3_4_5() { assert_eq!(Int(15), eval("1,2,3,4,5 :: sum")) }
	}

	mod zip {
		use super::*;
		#[test] fn _1_2_3__4_5_6() { assert_eq!(Value::from([[1,4],[2,5],[3,6]]), eval("1,2,3 4,5,6 :: zip")) }
		#[test] fn _1_2_3__4_5_6__reduce_add() { assert_eq!(Value::from([5,7,9]), eval("1,2,3 4,5,6 :: map reduce add _ _ _ zip")) }
		#[test] fn _1_2_3__4_5_6__sum() { assert_eq!(Value::from([5,7,9]), eval("1,2,3 4,5,6 :: map sum _ zip")) }
	}

	mod transpose {
		use super::*;
		#[test] fn _1_2_3__4_5_6() { assert_eq!(Value::from([[1,4],[2,5],[3,6]]), eval("1,2,3__4,5,6 :: transpose")) }
		#[test] fn _1_2__3_4__5_6() { assert_eq!(Value::from([[1,2,3],[4,5,6]]), eval("1,4__2,5__3,6 :: transpose")) }
	}

	mod abs {
		use super::*;
		#[test] fn _42() { assert_eq!(Int(42), eval("42 :: abs")) }
		#[test] fn _m42() { assert_eq!(Int(42), eval("-42 :: abs")) }
		#[test] fn _1_m2_3() { assert_eq!(Value::from([1,2,3]), eval("1,-2,3 :: abs")) }
	}

	mod dedup {
		use super::*;
		#[test] fn _1_2_3_3_3() { assert_eq!(Value::from([1,2,3]), eval("1,2,3,3,3 :: dedup")) }
	}

	mod dedup_by {
		use super::*;
		#[test] fn _1_2_3_3_3__eq() { assert_eq!(Value::from([1,2,3]), eval("1,2,3,3,3 :: dedup-by ==")) }
		// #[test] fn _1_2_3_3_3__?() { assert_eq!(Value::from([3,3,3]), eval("1,2,3,3,3 :: dedup-by ?")) } // TODO?
	}

	mod codedup {
		use super::*;
		#[test] fn _1_2_3_3_3() { assert_eq!(Value::from([3,3,3]), eval("1,2,3,3,3 :: codedup")) }
	}

	mod codedup_by {
		use super::*;
		#[test] fn _1_2_3_m3_m3__abs() { assert_eq!(Value::from([3,-3,-3]), eval("1,2,3,-3,-3 :: codedup-by != abs _ abs _")) }
	}

	mod first {
		use super::*;
		#[test] fn _4_5_6() { assert_eq!(Int(4), eval("4,5,6 :: first")) }
	}

	mod last {
		use super::*;
		#[test] fn _4_5_6() { assert_eq!(Int(6), eval("4,5,6 :: last")) }
	}

	mod chunks {
		use super::*;
		#[test] fn _1_2_3_4_5_6__2() { assert_eq!(Value::from([[1,2],[3,4],[5,6]]), eval("1,2,3,4,5,6 :: chunks 2")) }
		#[test] fn _1_2_3_4_5_6__3() { assert_eq!(Value::from([[1,2,3],[4,5,6]]), eval("1,2,3,4,5,6 :: chunks 3")) }
	}

	mod windows {
		use super::*;
		#[test] fn _1_2_3_4_5_6__2() { assert_eq!(Value::from([[1,2],[2,3],[3,4],[4,5],[5,6]]), eval("1,2,3,4,5,6 :: windows 2")) }
		#[test] fn _1_2_3_4_5_6__3() { assert_eq!(Value::from([[1,2,3],[2,3,4],[3,4,5],[4,5,6]]), eval("1,2,3,4,5,6 :: windows 3")) }
	}

	mod modulo {
		use super::*;
		#[test] fn _42_10() { assert_eq!(Int(2), eval("42 10 :: mod")) }
		#[test] fn _m42_10() { assert_eq!(Int(8), eval("-42 10 :: mod")) }
	}
	mod modulo_fake {
		use super::*;
		#[test] fn _42_10() { assert_eq!(Int(2), eval("42 10 :: modf")) }
		#[test] fn _m42_10() { assert_eq!(Int(-2), eval("-42 10 :: modf")) }
	}

	mod max {
		use super::*;
		#[test] fn _5_3_8_0_9_1_2_6_7_4() { assert_eq!(Int(9), eval("5,3,8,0,9,1,2,6,7,4 :: max")) }
	}
	mod min {
		use super::*;
		#[test] fn _5_3_8_0_9_1_2_6_7_4() { assert_eq!(Int(0), eval("5,3,8,0,9,1,2,6,7,4 :: min")) }
	}
	mod max2 {
		use super::*;
		#[test] fn _0__0() { assert_eq!(Int(0), eval("0 0 :: max2")) }
		#[test] fn _0__9() { assert_eq!(Int(9), eval("0 9 :: max2")) }
		#[test] fn _9__9() { assert_eq!(Int(9), eval("9 9 :: max2")) }
		#[test] fn _1_2_3__0() { assert_eq!(Int(3), eval("1,2,3 0 :: max2")) }
		#[test] fn _1_2_3__9() { assert_eq!(Int(9), eval("1,2,3 9 :: max2")) }
	}
	mod min2 {
		use super::*;
		#[test] fn _0__0() { assert_eq!(Int(0), eval("0 0 :: min2")) }
		#[test] fn _0__9() { assert_eq!(Int(0), eval("0 9 :: min2")) }
		#[test] fn _9__9() { assert_eq!(Int(9), eval("9 9 :: min2")) }
		#[test] fn _1_2_3__0() { assert_eq!(Int(0), eval("1,2,3 0 :: min2")) }
		#[test] fn _1_2_3__9() { assert_eq!(Int(1), eval("1,2,3 9 :: min2")) }
	}

	mod join {
		use super::*;
		#[test] fn int_int() { assert_eq!(Value::from([3,4]), eval("3 4 :: join")) }
		#[test] fn int_arr() { assert_eq!(Value::from([3,4,5,6]), eval("3 4,5,6 :: join")) }
		#[test] fn arr_int() { assert_eq!(Value::from([3,4,5,6]), eval("3,4,5 6 :: join")) }
		#[test] fn arr_arr() { assert_eq!(Value::from([3,4,5,6,7]), eval("3,4,5 6,7 :: join")) }
	}

	mod starling1 {
		use super::*;
		mod append_max {
			use super::*;
			#[test] fn _1_2_3__0() { assert_eq!(Value::from([1,2,3,3]), eval("1,2,3 0 :: s1 join _ _ max2")) }
			#[test] fn _1_2_3__1() { assert_eq!(Value::from([1,2,3,3]), eval("1,2,3 1 :: s1 join _ _ max2")) }
			#[test] fn _1_2_3__2() { assert_eq!(Value::from([1,2,3,3]), eval("1,2,3 2 :: s1 join _ _ max2")) }
			#[test] fn _1_2_3__3() { assert_eq!(Value::from([1,2,3,3]), eval("1,2,3 3 :: s1 join _ _ max2")) }
			#[test] fn _1_2_3__9() { assert_eq!(Value::from([1,2,3,9]), eval("1,2,3 9 :: s1 join _ _ max2")) }
		}
	}

	mod running {
		use super::*;
		#[test] fn max() { assert_eq!(Value::from([0,1,1,2,2,2,2,3,3,3]), eval("0,1,0,2,1,0,1,3,0,1 :: running max")) }
		#[test] fn min() { assert_eq!(Value::from([2,2,2,1,1,1,1,0,0,0]), eval("2,3,2,1,2,1,1,0,3,1 :: running min")) }
	}
	mod running2 {
		use super::*;
		mod sum {
			use super::*;
			#[test] fn _1_1_1_1() { assert_eq!(Value::from([1,2,3,4]), eval("1,1,1,1 :: running2 add")) }
			#[test] fn _1_2_3_4() { assert_eq!(Value::from([1,3,6,10]), eval("1,2,3,4 :: running2 add")) }
		}
		#[test] fn max() { assert_eq!(Value::from([0,1,1,2,2,2,2,3,3,3]), eval("0,1,0,2,1,0,1,3,0,1 :: running2 max2")) }
		#[test] fn min() { assert_eq!(Value::from([2,2,2,1,1,1,1,0,0,0]), eval("2,3,2,1,2,1,1,0,3,1 :: running2 min2")) }
	}

	mod violet_starling {
		use super::*;
		#[test] fn prepend_min() { assert_eq!(Value::from([1,1,2,3]), eval("1,2,3 :: sigma join _ _ min")) }
	}

	mod index_of {
		use super::*;
		mod max {
			use super::*;
			mod first {
				use super::*;
				#[test] fn _5_3_8_0_9_1_2_0_9_6_7_4() { assert_eq!(Int(4), eval("5,3,8,0,9,1,2,0,9,6,7,4 :: imaxf")) }
			}
			mod last {
				use super::*;
				#[test] fn _5_3_8_0_9_1_2_0_9_6_7_4() { assert_eq!(Int(8), eval("5,3,8,0,9,1,2,0,9,6,7,4 :: imaxl")) }
			}
		}
		mod min {
			use super::*;
			mod first {
				use super::*;
				#[test] fn _5_3_8_0_9_1_2_0_9_6_7_4() { assert_eq!(Int(3), eval("5,3,8,0,9,1,2,0,9,6,7,4 :: iminf")) }
			}
			mod last {
				use super::*;
				#[test] fn _5_3_8_0_9_1_2_0_9_6_7_4() { assert_eq!(Int(7), eval("5,3,8,0,9,1,2,0,9,6,7,4 :: iminl")) }
			}
		}
	}

	mod drop {
		use super::*;
		#[test] fn _3__3_1_4_1_5() { assert_eq!(Value::from([1,5]), eval("3,1,4,1,5 :: drop 3")) }
		#[test] fn _3_1_4_1_5__3() { assert_eq!(Value::from([1,5]), eval("3,1,4,1,5 :: drop _ 3")) }
	}
	mod take {
		use super::*;
		#[test] fn _3__3_1_4_1_5() { assert_eq!(Value::from([3,1,4]), eval("3,1,4,1,5 :: take 3")) }
		#[test] fn _3_1_4_1_5__3() { assert_eq!(Value::from([3,1,4]), eval("3,1,4,1,5 :: take _ 3")) }
	}

	mod head {
		use super::*;
		#[test] fn _9_8_7_6_5() { assert_eq!(Value::from([9,8,7,6]), eval("9,8,7,6,5 :: head")) }
	}
	mod tail {
		use super::*;
		#[test] fn _9_8_7_6_5() { assert_eq!(Value::from([8,7,6,5]), eval("9,8,7,6,5 :: tail")) }
	}

	mod phoenix {
		use super::*;
		#[test] fn add_sq_sqrt() { assert_eq!(Int(100_i64.pow(2) + 100_i64.isqrt()), eval("100 :: phi add _ _ sq _ sqrt _")) }
	}

	mod reverse {
		use super::*;
		#[test] fn _3_1_4_1_5() { assert_eq!(Value::from([5,1,4,1,3]), eval("3,1,4,1,5 :: rev")) }
	}
}


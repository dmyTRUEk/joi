//! joi - combinatory functional array programming language

#![deny(
	unreachable_patterns,
	unused_results,
	unused_variables,
)]

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
	// TODO?
	// #[arg(short='i', long, default_value_t=false)]
	// input_at_the_end: bool,

	// TODO: execute from file by filename

	program: Vec<String>,
}



fn main() {
	let CliArgs {
		program,
	} = CliArgs::parse();

	let result = eval(&program.join(" "));
	println!("result: {result:?}");
}





#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum Value {
	Int(i64),
	Array(Vec<Value>),
}
impl From<&str> for Value {
	fn from(s: &str) -> Self {
		use Value::*;
		// dbg!(s);
		if s.contains(',') {
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





#[derive(Debug)]
enum Function {
	Argument,
	Literal(Value),

	Warbler { a: Box<Function> },
	Cardinal { a: Box<Function> },
	Starling { ab: Box<[Function; 2]> },

	Identity { a: Box<Function> },
	Negate { a: Box<Function> },
	Square { a: Box<Function> },

	Add { ab: Box<[Function; 2]> },
	Subtract { ab: Box<[Function; 2]> },
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
		macro_rules! ab { () => (Box::new([Function::from_strs(tokens), Function::from_strs(tokens)])) }
		match tokens.remove(0) {
			"." => Argument,
			s if s.starts_with(['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']) || s.contains(',') => Literal(Value::from(s)),

			"w" => Warbler { a: a!() },
			"c" => Cardinal { a: a!() },
			"s" => Starling { ab: ab!() },

			"id" => Identity { a: a!() },
			"neg" => Negate { a: a!() },
			"sq" => Square { a: a!() },

			"add" => Add { ab: ab!() },
			"sub" => Subtract { ab: ab!() },

			t => panic!("unknown token: `{t}`")
		}
	}


	fn call(self, mut args: Vec<Value>) -> Value {
		let result = self.call_(&mut args);
		assert!(args.is_empty(), "NOT ALL ARGS ARE USED!");
		result
	}
	fn call_(self, args: &mut Vec<Value>) -> Value {
		use Function::*;
		use Value::*;
		match self {
			// 0
			Argument => args.remove(0),
			Literal(v) => v,

			// COMBINATORS ARITY 1
			Warbler { a } => {
				args.insert(0, args[0].clone());
				a.call_(args)
			}
			Cardinal { a } => {
				args.swap(0, 1);
				a.call_(args)
			}
			// COMBINATORS ARITY 2
			Starling { ab } => {
				let [a, b] = *ab;
				let first_arg = args[0].clone();
				let tmp_res = b.call_(args);
				args.insert(0, tmp_res);
				args.insert(0, first_arg);
				a.call_(args)
			}

			// FUNCTIONS ARITY 1
			Identity { a } => {
				a.call_(args)
			}
			Negate { a } => {
				match a.call_(args) {
					Int(n) => Int(-n),
					Array(_) => todo!()
				}
			}
			Square { a } => {
				match a.call_(args) {
					Int(n) => Int(n*n),
					Array(_) => todo!()
				}
			}

			// FUNCTIONS ARITY 2
			Add { ab } => {
				let [a, b] = *ab;
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int(a + b),
					_ => todo!()
				}
			}
			Subtract { ab } => {
				let [a, b] = *ab;
				match (a.call_(args), b.call_(args)) {
					(Int(a), Int(b)) => Int(a - b),
					_ => todo!()
				}
			}
		}
	}
}





fn eval(program: &str) -> Value {
	let tmp = program.split("::").collect::<Vec<_>>();
	let [args, fn_tokens] = tmp.as_slice() else { panic!() };
	let args: Vec<Value> = args
		.split(' ')
		.filter(|el| !el.is_empty())
		.map(Value::from)
		.collect();
	// dbg!(&args);
	// dbg!(fn_tokens);
	let function = Function::from_str(fn_tokens);
	dbg!(&function);
	function.call(args)
}





#[cfg(test)]
mod eval {
	use super::*;
	use Value::*;
	#[test]
	fn arg_implicit() {
		assert_eq!(
			Int(2),
			eval("2 ::")
		)
	}
	#[test]
	fn arg_explicit() {
		assert_eq!(
			Int(2),
			eval("2 :: .")
		)
	}
	#[test]
	fn const_2() {
		assert_eq!(
			Int(2),
			eval(":: 2")
		)
	}
	#[test]
	fn identity() {
		assert_eq!(
			Int(2),
			eval("2 :: id")
		)
	}
	#[test]
	fn neg() {
		assert_eq!(
			Int(-2),
			eval("2 :: neg")
		)
	}
	#[test]
	fn neg_neg() {
		assert_eq!(
			Int(-(-2)),
			eval("2 :: neg neg")
		)
	}
	#[test]
	fn square() {
		assert_eq!(
			Int(3*3),
			eval("3 :: sq")
		)
	}
	#[test]
	fn add() {
		assert_eq!(
			Int(2+2),
			eval("2 2 :: add")
		)
	}
	#[test]
	fn sub() {
		assert_eq!(
			Int(2-3),
			eval("2 3 :: sub")
		)
	}
	#[test]
	fn neg_add() {
		assert_eq!(
			Int(-(2+2)),
			eval("2 2 :: neg add")
		)
	}
	#[test]
	fn add_neg_arg_neg() {
		assert_eq!(
			Int(-2-3),
			eval("2 3 :: add neg . neg")
		)
	}

	#[test]
	fn warbler() {
		assert_eq!(
			Int(2+2),
			eval("2 :: w add")
		)
	}
	#[test]
	fn warbler_() {
		assert_eq!(
			Int(2+2),
			eval("2 :: add w")
		)
	}
	#[test]
	fn cardinal() {
		assert_eq!(
			Int(3-2),
			eval("2 3 :: c sub")
		)
	}
	#[test]
	fn starling_add_sq() {
		assert_eq!(
			Int(3 + 3*3),
			eval("3 :: s add sq")
		)
	}
	#[test]
	fn starling_sub_arg_arg_sq() {
		assert_eq!(
			Int(3 - 3*3),
			eval("3 :: s sub . . sq")
		)
	}
}


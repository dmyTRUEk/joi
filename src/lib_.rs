//! lib_



pub trait CoDedup<T> where Self: Sized {
	fn codedup(self) -> Self;
	fn codedup_by(self, cmp: impl FnMut(&T, &T) -> bool) -> Self;
}
impl<T: Clone + PartialEq> CoDedup<T> for Vec<T> {
	fn codedup(self) -> Self {
		if self.is_empty() { return self }
		let mut res = vec![];
		let mut iter = self.into_iter();
		let mut prev = iter.next().unwrap();
		let mut just_pushed = false;
		for el in iter {
			if prev != el {
				prev = el;
				just_pushed = false;
				continue
			}
			if !just_pushed {
				res.push(prev.clone());
				just_pushed = true;
			}
			res.push(el);
		}
		res
	}
	fn codedup_by(self, mut cmp: impl FnMut(&T, &T) -> bool) -> Self {
		if self.is_empty() { return self }
		let mut res = vec![];
		let mut iter = self.into_iter();
		let mut prev = iter.next().unwrap();
		let mut just_pushed = false;
		for el in iter {
			if cmp(&prev, &el) {
				prev = el;
				just_pushed = false;
				continue
			}
			if !just_pushed {
				res.push(prev.clone());
				just_pushed = true;
			}
			res.push(el);
		}
		res
	}
}

#[cfg(test)]
mod codedup {
	use super::*;
	#[test] fn _1() { assert_eq!(Vec::<i32>::new(), vec![1].codedup()) }
	#[test] fn _3_3_3() { assert_eq!(vec![3,3,3], vec![3,3,3].codedup()) }
	#[test] fn _1_2_3_3_3() { assert_eq!(vec![3,3,3], vec![1,2,3,3,3].codedup()) }
	#[test] fn _3_3_3_2_1() { assert_eq!(vec![3,3,3], vec![3,3,3,2,1].codedup()) }
	#[test] fn _1_2_3_3_3_4_5_6_7_7() { assert_eq!(vec![3,3,3,7,7], vec![1,2,3,3,3,4,5,6,7,7].codedup()) }
}
#[allow(non_snake_case)]
#[cfg(test)]
mod codedup_by {
	use super::*;
	#[test] fn _1__abs() { assert_eq!(Vec::<i32>::new(), vec![1_i32].codedup_by(|a, b| a.abs() != b.abs())) }
	#[test] fn _3_3_3__abs() { assert_eq!(vec![3,3,3], vec![3,3,3_i32].codedup_by(|a, b| a != b)) }
	#[test] fn _1_2_3_3_3__abs() { assert_eq!(vec![3,3,3], vec![1,2,3,3,3_i32].codedup_by(|a, b| a != b)) }
	#[test] fn _1_2_m3_3_3__abs() { assert_eq!(vec![-3,3,3], vec![1,2,-3,3,3_i32].codedup_by(|a, b| a.abs() != b.abs())) }
	#[test] fn _1_2_3_m3_3__abs() { assert_eq!(vec![3,-3,3], vec![1,2,3,-3,3_i32].codedup_by(|a, b| a.abs() != b.abs())) }
	#[test] fn _1_2_3_3_m3__abs() { assert_eq!(vec![3,3,-3], vec![1,2,3,3,-3_i32].codedup_by(|a, b| a.abs() != b.abs())) }
	#[test] fn _1_2_3_m3_m3_4_5_6_m7_7() { assert_eq!(vec![3,-3,-3,-7,7], vec![1,2,3,-3,-3,4,5,6,-7,7_i32].codedup_by(|a, b| a.abs() != b.abs())) }
}





pub fn transpose<T: Clone>(vecs: Vec<Vec<T>>) -> Vec<Vec<T>> {
	let min_len = vecs.iter().map(|v| v.len()).min().unwrap();
	let mut res = vec![];
	for i in 0..min_len {
		let mut tmp = Vec::with_capacity(vecs.len());
		for v in vecs.iter() {
			tmp.push(v[i].clone())
		}
		res.push(tmp);
	}
	res
}

#[allow(non_snake_case)]
#[cfg(test)]
mod transpose {
	use super::*;
	#[test] fn _1_2_3__4_5_6() { assert_eq!(vec![vec![1,4],vec![2,5],vec![3,6]], transpose(vec![vec![1,2,3],vec![4,5,6]])) }
	#[test] fn _1_2__3_4__5_6() { assert_eq!(vec![vec![1,2,3],vec![4,5,6]], transpose(vec![vec![1,4],vec![2,5],vec![3,6]])) }
}



pub trait IndexOfMaxMin {
	fn index_of_max_first(&self) -> usize;
	fn index_of_max_last(&self) -> usize;
	fn index_of_min_first(&self) -> usize;
	fn index_of_min_last(&self) -> usize;
}
impl<T: PartialOrd> IndexOfMaxMin for Vec<T> {
	fn index_of_max_first(&self) -> usize {
		let mut index_of_max_first = 0;
		let (mut max, v) = self.split_first().unwrap();
		for (i, el) in v.iter().enumerate() {
			if el > max {
				max = el;
				index_of_max_first = i + 1; // +1 bc we popped first element
			}
		}
		index_of_max_first
	}
	fn index_of_max_last(&self) -> usize {
		let mut index_of_max_last = 0;
		let (mut max, v) = self.split_first().unwrap();
		for (i, el) in v.iter().enumerate() {
			if el >= max {
				max = el;
				index_of_max_last = i + 1; // +1 bc we popped first element
			}
		}
		index_of_max_last
	}
	fn index_of_min_first(&self) -> usize {
		let mut index_of_min_first = 0;
		let (mut min, v) = self.split_first().unwrap();
		for (i, el) in v.iter().enumerate() {
			if el < min {
				min = el;
				index_of_min_first = i + 1; // +1 bc we popped first element
			}
		}
		index_of_min_first
	}
	fn index_of_min_last(&self) -> usize {
		let mut index_of_min_last = 0;
		let (mut min, v) = self.split_first().unwrap();
		for (i, el) in v.iter().enumerate() {
			if el <= min {
				min = el;
				index_of_min_last = i + 1; // +1 bc we popped first element
			}
		}
		index_of_min_last
	}
}
#[cfg(test)]
mod index_of {
	use super::*;
	mod max {
		use super::*;
		mod first {
			use super::*;
			#[test] fn _5_3_8_0_9_1_2_0_9_6_7_4() { assert_eq!(4, vec![5,3,8,0,9,1,2,0,9,6,7,4].index_of_max_first()) }
		}
		mod last {
			use super::*;
			#[test] fn _5_3_8_0_9_1_2_0_9_6_7_4() { assert_eq!(8, vec![5,3,8,0,9,1,2,0,9,6,7,4].index_of_max_last()) }
		}
	}
	mod min {
		use super::*;
		mod first {
			use super::*;
			#[test] fn _5_3_8_0_9_1_2_0_9_6_7_4() { assert_eq!(3, vec![5,3,8,0,9,1,2,0,9,6,7,4].index_of_min_first()) }
		}
		mod last {
			use super::*;
			#[test] fn _5_3_8_0_9_1_2_0_9_6_7_4() { assert_eq!(7, vec![5,3,8,0,9,1,2,0,9,6,7,4].index_of_min_last()) }
		}
	}
}


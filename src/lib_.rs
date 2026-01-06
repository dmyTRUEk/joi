//! lib_

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


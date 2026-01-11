# Joi
Array + Combinatory + Functional programming language

## Example 1: sum of squares
```joi
1,2,3,4 :: sum sq
> 30
```

## Example 2: [leetcode 1920](https://leetcode.com/problems/build-array-from-permutation/) - array permutation
```joi
0,2,1,5,3,4 :: w at
> 0,1,2,4,5,3
```

## Example 3: [leetcode 961](https://leetcode.com/problems/n-repeated-element-in-size-2n-array/) - find repeated element
```joi
5,1,5,2,5,3,5,4 :: first codedup sort
> 5
```

## Example 4: [leetcode 3190](https://leetcode.com/problems/find-minimum-operations-to-make-all-elements-divisible-by-three/) - min num of ops to be div by 3
```joi
1,2,3,4 :: sum map != 3
> 3
```

## Example 5\*: [leetcode 42](https://leetcode.com/problems/trapping-rain-water/) - trapping rain water
```joi
4,2,0,3,2,5 :: phi~
  add _ _
  sum sigma sub _ _ scan2 max2 _ _ _ _
  s take imaxf _ _ _ _
  s take imaxl rev
> 9
```


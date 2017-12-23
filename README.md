# Data Structures for Idris

Experiments in implementing data structures in the dependently typed programming language [Idris](https://www.idris-lang.org).

Notably missing:

- Instances of `Eq`, `Ord`, `Functor`, `Applicative`, `Monad`, `Traversable`, `Show`, `DecEq`
- Efficient dictionaries (these are a generalization of sets)
- Benchmarks

For now these are left as a proverbial 'exercise for the reader'.

# Table of Contents

* [Data Structures for Idris](#data-structures-for-idris)
* [Dependently Typed Lists](#dependently-typed-lists)
  * [OrderedVect](#orderedvect)
  * [VectRankedElem](#vectrankedelem)
* [Okasaki's Purely Functional Data Structures](#okasakis-purely-functional-data-structures)
  * [LeftistHeap](#leftistheap)
  * [MergeList](#mergelist)
  * [LazyPairingHeap](#lazypairingheap)
  * [Queue](#queue)
  * [BinarySearchTree](#binarysearchtree)
  * [RandomAccessList](#randomaccesslist)

# Dependently Typed Lists

## OrderedVect

`OrderedVect` is a linked list type that is always sorted. The element count and order criteria are embedded in the type. There's also a `merge` operation that will merge two `OrderedVect`s.

Available operations: `merge`, `head`, `tail`, `orderedVectToList`

## VectRankedElem

In Idris, `Elem 2 [1, 2, 3, 4]` is satisfied by a proof that `2` is an element of `[1, 2, 3, 4]`. There is only one such proof:

```
Idris> the (Elem 2 [1,2,3,4]) (There Here)
There Here : Elem 2 [1, 2, 3, 4]
```

The module `VectRankedElem` contains a type `RankedElem` that is similar but also encodes the index where the element is found:

```
Idris> the (RankedElem 2 [1,2,3,4] 1) (There Here)
There Here : RankedElem 2 [1, 2, 3, 4] 1
```

The module also contains a few functions that use `RankedElem` to prove interesting properties:

- `cons_ x xs` returns `(x::xs)` as well as a proof that for every `RankedElem el xs i` there is a `RankedElem el (x::xs) (S i)` and a proof of `RankedElem x (x::xs) Z`
- `concat_ xs ys` returns `xs ++ ys` as well as a proof that for every `RankedElem el xs i` there is a `RankedElem el (xs ++ ys) i` and a proof that for every `RankedElem el ys i` there is a `RankedElem el (length xs + i) i`
- `rev_ xs` returns `reverse xs` as well as a proof that for every `RankedElem el xs i` there is a `RankedElem el (reverse xs) (length xs - i)`

The module also contains functions `cons`, `concat`, `rev` that call their `_` counterpart and return only data. These functions behave entirely like `::`, `++`, `reverse`.

The proofs returned by `cons_`, `concat_`, `rev_` can be composed to prove properties on more complicated data structures.

# Okasaki's Purely Functional Data Structures

The data structures in this section are inspired by Chris Okasaki's book [Purely Functional Data Structures](https://books.google.com.sg/books/about/Purely_Functional_Data_Structures.html?id=SxPzSTcTalAC&redir_esc=y). This book is based on Okasaki's PhD Thesis, which is available as a free [PDF](https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf).

## LeftistHeap

Using dependent types I was able to prove the following:

- `LeftistHeap` is always sorted
- `LeftistHeap` respects the 'leftist property'
- The result of merging a `LeftistHeap` of length `m` and a heap of length `n` is a heap of length `m + n`
- `insert` and `deleteMin` yield a `LeftistHeap` that has one element more or less (respectively) than the input heap

Available operations: `findMin`, `merge`, `insert`, `deleteMin`.

A supplementary `CountedLeftistHeap` data structure is also available.

## MergeList

`MergeList` is a dependently typed 'bottom up merge sort' data structure. A merge list is a linked list of `OrderedVect`s, strictly ordered by size, and where each `OrderedVect` has a size expressible as 2ⁿ. For example, `[[10], [3, 6, 9, 12]]` and `[[10], [5, 8], [3, 6, 9, 12]]` are valid `MergeList`s.

Available operations: `insert`, `mergeListToOrderedVect`

By using dependent types we get the following guarantees:

- The `OrderedVect`s have sizes that are expresible as 2ⁿ and are strictly ordered by size
- A `MergeList` of a given size can be flattened into an `OrderedVect` of the same size
- When inserting `n` elements, the resulting merge list has `n` elements more than the input merge list

## LazyPairingHeap

`LazyPairingHeap` is another ordered list data structure. We have the following guarantees:

- Elements are ordered
- Inserting and removing elements changes the size of the heap as expected

Available operations: `findMin`, `merge`, `insert`, `deleteMin`

## Queue

The type `Queue` is a functional queue data struture. It consist of a 'front list' `f` and a 'reverse list' `r` that together represent the logical list `f ++ reverse r`. Moreover, for reasons of efficiency, it is an invariant that `r` is never larger than `f`.

Available operations: `head`, `snoc_`, `snoc`, `tail_`, `tail`

Similar to what was done in `VectRankedElem` (see above), `snoc_` and `tail_` return functions that map proofs about the original queue onto proofs about the new queue.

We have proofs for the following properties:

- The reverse list is never larger than the front list
- `snoc_` preserves the existence and the index of all elements and it adds the new element to the end of the queue
- `tail_` drops the first element and shifts the indices of the remaining elements by 1

`snoc` and `tail` are simple wrappers around `snoc_` and `tail_` that return the new queue, but not the proofs.

## BinarySearchTree

`BinarySearchTree` is an implementation of functional binary trees.

Available operations: `decElem`, `elem`, `insert`

The above operations are based on a higher order function named `find`. `find` takes a needle and a function for arguments. `find` efficiently recurses over the tree trying to find the needle. At every step it returns the result of calling `f` with (a) contextual information about the search process and (b) the result of the previous step. The search context includes a verified upper and lower bound for the current node, by which `find` can prove to `f` that it's traversing the tree correctly.

## RandomAccessList

`RandomAccessList` is a list structure that provides efficient prepend and access to element at arbitrary indices. Informally you can think of it as a persistent array.

The namespace `Data.RandomAccessList` contains `RandomAccessList` and `CountedRandomAccessList` types. They allow the following operations:

- `cons` for prepending an element
- `tail` for removing the first element
- `index` for accessing an element at a specific index
- `update` for updating an element at a specific index

These operations take O(log<sub>n</sub>) time. See Okasaki's book for techniques to reduce the time complexity to constant time.

By construction all accesses and updates to a `RandomAccessList` are proved to be safe.

Usually arrays allow efficient append and prepend is expensive. In `RandomAccessList`, prepend is cheap and append is expensive. The performance of these operations can be swapped by translating all indices. That is, `cons` can be interpreted as an append and access to indices can be translated as follows: `realIndex(virtualIndex) = size - 1 - virtualIndex`,

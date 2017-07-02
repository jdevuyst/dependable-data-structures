# Data Structures for Idris

Experiments in implementing data structures in the dependently typed programming language [Idris](https://www.idris-lang.org).

I used Chris Okasaki's [Purely Functional Data Structures](https://books.google.com.sg/books/about/Purely_Functional_Data_Structures.html?id=SxPzSTcTalAC&redir_esc=y) as a starting point. This book is based on Okasaki's PhD Thesis, which is available as a free [PDF](https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf).

## Leftist Heap

Using dependent types I was able to prove the following:

- `LeftistHeap` is always sorted
- `LeftistHeap` respects the 'leftist property'
- The result of merging a `LeftistHeap` of length `m` and a heap of length `n` is a heap of length `m + n`
- `insert` and `deleteMin` yield a `LeftistHeap` that has one element more or less (respectively) than the input heap

Available operations: `findMin`, `merge`, `insert`, `deleteMin`.

A supplementary `CountedLeftistHeap` data structure is also available.

## OrderedVect

`OrderedVect` is a linked list type that is always sorted. The element count and order criteria are embedded in the type. There's also a `merge` operation that will merge two `OrderedVect`s.

Available operations: `merge`, `head`, `tail`, `orderedVectToList`

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
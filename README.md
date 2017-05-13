# Data Structures for Idris

Experiments in implementing data structures in the dependently typed programming language [Idris](https://www.idris-lang.org).

I used Chris Okasaki's [Purely Functional Data Structures](https://books.google.com.sg/books/about/Purely_Functional_Data_Structures.html?id=SxPzSTcTalAC&redir_esc=y) as a starting point. This book is based on Okasaki's PhD Thesis, which is available as a free [PDF](https://www.cs.cmu.edu/~rwh/theses/okasaki.pdf).

## Leftist Heap

Using dependent types I was able to prove the following:
- `LeftistHeap` is always sorted
- `LeftistHeap` respects the 'leftist property'
- The result of merging a `LeftistHeap` of length `m` and a heap of length `n` is a heap of length `m + n`

Available operations: `findMin`, `merge`, `insert`, `deleteMin`.

A supplementary `CountedLeftistHeap` data structure is also available. 
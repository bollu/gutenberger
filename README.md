# Gutenberger: A solver for presburger arithmetic using finite automate encodings

Presburger arithmetic is first order logic (forall, there exists) over real
numbers, equipped with `(+, -, >=, <=, !=)` (notice the lack of multiplication.

The implementation is done based on the description from the (excellent) description
in the lecture notes 
[Automata theory: an algorithmic approach](https://www7.in.tum.de/~esparza/autoskript.pdf)
(Chapter 10: Applications III - presburger arithmetic).

The haskell implementation has `quickcheck` tests that generate random
examples and check that the implementation is correct.


The current haskell implementation uses notions of NFAs and DFAs that are
honestly too strong for what we care about. We can compute much of the
inforomation lazily --- for example, the universe state space. We also do not
need to compute some values such as the set of final states, since can be
cheaply tested for. 

The implementation should be much much faster if done in C/C++, which is what I
plan on doing next.

The drawback of this approach is that we are left with an _oracle_, with no
notion of the geometry of the set left behind anymore. So while we can
answer emptiness queries, and queries of whether a point belongs in a presburger
set very efficiently, questions such as "what are the vertices of the set"
are not answerable.

I do not know a reference off-hand on how to convert this oracle back to
its geometric description. A pointer to this would be invaluable.


## Building from source (haskell) 

use `cabal` to build. That is,

```
$ cabal v2-build
$ cabal v2-repl
> main -- to run unit tests & QuickCheck tests
```

## Building from source (cpp)

Recommend setting up the `post-commit` hook so the docs auto-build:


To build, use `cmake` with `make/ninja`:

```
$ mkdir build && cd build && cmake ../ && make
```

```
$ mkdir build && cd build && cmake -Gninja ../ && ninja
```

For autocompletion, I use `YouCompleteMe` along with `cmake`'s ability
to generate autocomplete information as follows:

```
$ cd build && cmake -DCMAKE_EXPORT_COMPILE_COMMANDS=ON ../
$ cp compile_commands.json ../
```


# Reading
- [Automata theory: an algorithmic approach](https://www7.in.tum.de/~esparza/autoskript.pdf)
- [Mixed and Integer Linear Programming Using Automata Techniques](http://pi.math.cornell.edu/~minnes/Automata/AutDec.pdf)
- [An Automata-Theoretic Approach to Presburger Arithmetic Constraints](https://orbi.uliege.be/bitstream/2268/74877/1/WB95.pdf)


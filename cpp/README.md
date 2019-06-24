# Gutenberger: A solver for presburger arithmetic using finite automate encodings

Presburger arithmetic is first order logic (forall, there exists) over real
numbers, equipped with `(+, -, >=, <=, !=)` (notice the lack of multiplication.

This allows us to ask about ILP problems.
## Building from source

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
- [Mixed and Integer Linear Programming Using Automata Techniques](http://pi.math.cornell.edu/~minnes/Automata/AutDec.pdf)
- [An Automata-Theoretic Approach to Presburger Arithmetic Constraints](https://orbi.uliege.be/bitstream/2268/74877/1/WB95.pdf)


Advent of Code 2021 in Coq
==========================

Solutions for [Advent of Code 2021](https://adventofcode.com/2021) written in Coq,
a purely functional programming language where we can also prove theorems about
functions. Some of the solutions include proofs.

## Run code

Dependencies:
- Coq (tested with Coq 8.13)
- coq-stdpp

```shell
# Install dependencies
opam install coq-stdpp

# Run
cd src/

./a.sh aoc01.v aoc01_input.txt solve12  # Pair of answers for Day 1: Part One and Part Two
```

## Notes

### Execution

All answers are computed by direct evaluation, with `Compute solve x.`,
no extraction.

### Parsing

Where possible, the input is just included within a Coq file:

```
Definition x := input
<insert raw input here>
.
```

This leverages *notations*, user-defined extensions of Coq's grammar.

When this is not possible (9 days out of 25), we preprocess the input---with
scripts named `src/aocXX_input.txt.prep`, in various way:

- quote the whole input, inserting `"` at the beginning and end: days 8, 10, 16
- quote the input line-by-line: days 20, 25
- quote alphanumeric substrings: days 12, 14
- remove periods (Conflicts with Coq syntax): day 23

### Proving

A few of the solutions have some associated specifications and proofs.

#### Day 1

Part 2 involves computing sums in a sliding window `x[i]+x[i+1]+x[i+2]` over
the input sequence `x` and counting how many times the sums increase. This
algorithm can be fused to avoid computing each sum, by instead comparing every
element `x[i]` with `x[i+3]`.
`aoc01.v` contains a proof that these two methods produce the same result.

#### Day 2

The "aim" in Part 2 behaves the same as the "depth" in Part 1.
This is "obvious" from looking at the code, since each Part's respective functions
involve the same operations. `aoc02.v` makes that correspondence formal using
the concept of "simulation", and it occurred to me that only formal methods
people know what that means.

#### Day 7

`aoc07.v` contains a proof that Part 2 finds the minimum-cost
solution in the range `[0,xmax]` where `xmax` is the maximum position in the input
(theorem `solve2_correct`).
This result could be further improved to show that the solution is a global minimum.

Part 2 is about finding the minimum of a convex function, which we do by
binary search. The proof is decomposed as follows:

1. The cost function is convex (theorem `Convex_fuel2`).
2. Convex functions are V-shaped ("down then up", theorem `VShaped_Conves`)
3. Binary search (defined in that file) finds the minimum of V-shaped
   functions in a given range (`searchMin_correct`)

#### Day 8

`aoc08.v` contains a correctness specification (a formal statement but no proof)
of the core function in the solution, `decipher_line`:
if an input line `l` is obtained from scrambling some initial string of digits (`outs ls`),
then `decipher_line` computes the value of that input (reading the digits as a whole number).

That specification says nothing about applying the function to an invalid input
(one that is not obtained from scrambling some initial value). The solution is currently
"garbage in, garbage out"; it could be improved to detect ill-formed inputs,
and this could be specified accordingly.

#### Day 10

`aoc10.v` contains a full correctness theorem for the parser `check`.

- If the parser succeeds on an input `s`, it produces a stack `z` which can be
  used to complete `s` into  a well-bracketed string.

- If the parser fails on an input `s`, it produces the first mismatched character `c`,
  which is characterized by the property that prefixes of `s` **not** including `c` it can be
  completed into a well-bracketed string, while no prefix that **does** include
  `c` can be so completed.

#### Day 11

This problem relies on the property that it does not matter in what order
octopuses flash, the resulting state after each step (after resolving all
flashes) is uniquely determined. This property is called confluence.

Specifications only, no proofs. `aoc11.v` contains:

- a relation `one_flash` describing the effect of one octopus flashing,
  chosen non-deterministically.
- a specification that `one_flash` is *strongly confluent*: intuitively,
  if octopus A flashed then octopus B flashed, the resulting state is the same
  as if B flashed then A flashed.
- the above implies that the normal form of `one_flash` is uniquely determined
  (this is not stated), then `step_correct` says that the `step` function finds
  that normal form.

#### Day 19

Basically an exhaustive search. The solution uses an optimization: when trying
to match two scanners, while trying a given orientation, we want to find
a matching translation, and rather than enumerating the candidate translations,
we can enumerate the candidate translation vectors (all possible pairwise
differences between the two sets of beacons) and find the one that occurs at least 12 times.

`aoc19.v` contains a specification for this optimization, i.e.,
it doesn't affect functional behavior (theorem `try_match_correct`,
specification only, with an incomplete proof).

Specifying and verifying this is especially tricky because there might be
multiple matches. The problem statement guarantees uniqueness, but it's still
a pain to formally reason about.

#### Day 22

Efficiency is achieved by only manipulating cubes, as an implicit representation
of the huge space of individual points with on-off states. `aoc22.v` contains
a (mostly complete) proof of the correspondence between these implicit and
explicit representations.

- Top-level theorem (`vol_add_spec`): the solution (left-hand side) computes
  the number of on-switches after applying every operation (right-hand side).

- The main invariant for the core algorithm is that it maintains a list of cubes
  which represents an "inclusion-exclusion formula" (`inclexcl`) equivalent to
  the set operations applied to far (set union for "switch on" and set
  difference for "switch off"). In particular, that formula guarantees that
  set differences `A \ B` only occur when `B` is a subset of `A`
  (`nested_cubes` invariant). The preservation of those invariants by the step
  function `add_cube` is given by the two theorems `add_cube_nested` and
  `add_cube_spec`.

- The proof is mostly complete, missing the lemma that the volume of a cuboid
  is the product of its three sides.

#### Day 24

This solution relies on the observation that the input actually consists of 14
iterations of the same sequences of instruction differing only in three parameters,
These parameters are easily extracted ("decompiled") by pattern-matching.
Then they can be interpreted directly with a small arithmetic expression (`step`).
`aoc24.v` contains a proof that those parameters can be "compiled" back into
the original sequence, and also that `step` computes the same function as the
original ALU instructions. (This "decompilation" doesn't actually change
the asymptotic complexity of the solution but I only realized that later,
and the constant factor reduction is probably worthwhile anyway.)

A specification (no proof) of the final search algorithms is also given: we
find the lexicographically greatest/smallest input accepted by the program.

#### Extra comments

Among the days with no spec, some I think are either easy or interesting are:

- Days 6, 12, 21: Your typical dynamic programming problems.

- Day 14: A simple enough but not-too-trivial change of representation.

- Day 15: Verify Dijkstra's algorithm.

- Day 18: Is snailfish addition guaranteed to terminate?

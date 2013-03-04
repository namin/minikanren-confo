# Why?

I implemented `core.logic.nominal` to integrate (1) relational, (2)
constraint-based and (3) nominal techniques in one tool. Each of these
techniques is independently useful for exploring semantics of
programming languages and type systems. (1) If you implement your type
system as a relational program, you get not only a type checker, but
also a generator of well-typed terms, and possibly a type
inferencer. (2) If you express the rules of your type system as
constraints, and are able to monitor those constraints, then you can
possibly turn your type checker into a type debugger. (3) Nominal
abstract syntax simplfies reasoning about names and bindings so that you
can use the same conventions in your implementation as on paper.


# Nominal Logic Programming

Nominal logic programming brings nominal abstract syntax to logic
programming. Nominal abstract syntax is a technique for reasoning about
scope and binding, which is fairly close to what is done "on paper".  On
paper, one uses explicit names for bound variables, while assuming the
choice of name is unimportant, as long as the binding structure is
preserved.

Nominal abstract syntax formalizes this paper intuition, making it
easier to write programs, such as type inferencers and interpreters,
that must reason about scope and binding. Furthermore, nominal logic
programming maintains the intuitive reasoning about scope and binding of
nominal abstract syntax, even in the presence of unbound logic
variables.

## Reasoning about scope

Consider the lambda calculus, `e := x | (e e) | λx.e`.

A λ-term is a _binder_ because it _binds_ a name `x` in the term
`e`. Intuitively, the choice of the _bound_ names are unimportant, as
long as the same binding structure is represented, e.g.  `λa.a ≡α λb.b`
and `λa.λb.a ≡α λb.λa.b` but `λa.λb.a ≢α λb.λa.b`.

This intuitive notion of equality for binders is known as
α-equivalence. Formally, `λa.e ≡α λb.[b/a]e` where `b` does not occur
free in `e`.

The side-condition in the definition of α-equivalence is a _freshness
constraint_. Indeed, `λa.a ≢α λb.a` because `a` is bound in `λa.a` and
_free_ in `λb.a`.

These two useful notions, α-equivalence and freshness constraints, are
built into nominal logic programming. They enable programmers to reason
about scope and binding, even in the presence of unbound logic
variables, common in logic programs.

## Example: capture-avoiding substitution

## The three constructs of `core.logic.nominal`

core.logic.nominal extends core.logic with three constructs for nominal
logic programming: `fresh`, `tie`, and `hash`.

### `nom/fresh`

The operator `nom/fresh` introduces new names, just like `fresh` introduces
new variables.

A "nom" only unifies with itself or with an unbound variable.

A reified nom consists of the symbol `a` subscripted by a number: `a_0`, `a_1`, etc.

### `nom/tie`

The term constructor `nom/tie` binds a nom in a term. Binders are
unified up to alpha-equivalence.

### `nom/hash`

The operator `nom/hash` introduces a _freshness constraint_, asserting
that a nom does not occur _free_ in a term.

## Example: type inferencer

## Run your research!

### Example: type debugger

### Example: generator of counterexamples to meta-theoretic properties

## Under the hood: swapping!

Nominal unification is specified using nom-swaps and `#`-constraints.

Two binders `t1` and `t2` unify when either:

* `t1` is `[a] c1`, `t2` is `[a] c2` and `c1` unifies with `c2`, or
* `t1` is `[a] c1`, `t2` is `[b] c2`, `a#c2`, and `c1` unifies with the
  term `c2` with all `a`s and `b`s swapped.

Swapping introduces suspensions, because when we encounter a variable
during swapping, we must delay the swap until the variable is bound.

In core.logic.nominal, we implement suspensions as constraints. During
swapping of `a` and `b`, whenever we encounter a variable `x`, we
replace it with a fresh variable `x'` and add the suspension constraint
swap `[a b] x' x`. This swap constraint is executed under one of two
conditions:

* `x` and `x'` both become bound -- the swapping can resume
* `x` and `x'` become equal -- we enforce `a#x'` and `b#x'` and drop the
  swap constraint

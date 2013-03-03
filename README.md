# Nominal Logic Programming

Nominal logic programming extends logic programming with facilities to
explicitly manage names and bindings, making it easier to write
programs, such as type inferencers and interpreters, that must reason
about scope.

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

## Under the hood: swapping!

TODO

## Run your research!

TODO

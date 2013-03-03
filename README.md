# Nominal Logic Programming

## Introduction

core.logic.nominal extends core.logic with three constructs for nominal
logic programming: `fresh`, `tie`, and `hash`.

### `nom/fresh`

The operator `nom/fresh` introduces new names, just like `fresh` introduces
new variables.

A "nom" only unifies with itself or with an unbound variable.

A reified nom consists of the symbol `a` subscripted by a number: `a_0`, `a_1`, etc.

### `nom/tie`

The term constructor `nom/tie` binds a nom in a term.

### `nom/hash`

The operator `nom/hash` introduces a _freshness constraint_, asserting
that a nom does not occur free in a term.

## Some examples

### Capture-Avoiding Substitution

### Type Inferencer

## Under the hood: swapping!

## Run your research!

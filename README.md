# Nominal Logic Programming

## Introduction

core.logic.nominal extends core.logic with three constructs for nominal
logic programming: `fresh`, `hash`, and `tie`.

### `nom/fresh`

The operator `nom/fresh` introduces new names, just like `fresh` introduces
new variables.

A "nom" only unifies with itself or with an unbound variable.

A reified nom consists of the symbol `a` subscripted by a number.


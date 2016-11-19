# logexp
Logic over Expression

## What is logexp
Mathematical expression handling on top of the Prolog language.

## Status
Very experimental.

## Usage
Target environment is swi-prolog.

```prolog
?- use_package(engine).
?- use_package(axiom, []).
?- equiv(x+x, 2*x).
true.
```

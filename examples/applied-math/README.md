# Applied-math examples for the Axiom language

Ten small, commented sessions that show how Axiom's interpreter language
and its SPAD library language are used across applied mathematics. Each
`.input` file is a script you can run on its own:

```
axiom -nox                     # or: fricas -nosman
)read 03-ode-mechanics.input
```

All files were run end to end with FriCAS 1.3.10 (the actively maintained
fork of Axiom, which uses the same language). Output from Axiom itself may
be formatted a little differently.

| File | Domain | What it shows |
|------|--------|---------------|
| `01-types-and-domains.input` | The type system | `Fraction Integer`, `Float` with `digits`, `PrimeField 7`, factoring over ℤ vs ℤ[i], typed matrices |
| `02-calculus-and-series.input` | Analysis | `D`, `limit`, Risch `integrate`, improper integrals, Taylor/Puiseux `series`, closed-form `sum` |
| `03-ode-mechanics.input` | ODEs / mechanics | damped oscillator, initial value problems, resonance, logistic equation, `seriesSolve` (Airy) |
| `04-linear-algebra-vibrations.input` | Linear algebra | normal modes of coupled springs: characteristic polynomial, exact and numerical eigenvalues, `nullSpace` |
| `05-groebner-optimization.input` | Optimisation / algebraic geometry | Lagrange multipliers solved via a lexicographic Groebner basis and `radicalSolve`; intersecting conics; numerical system roots |
| `06-orthogonal-polys-quadrature.input` | Numerical analysis | Legendre orthogonality, building a 3-point Gauss rule exactly, Chebyshev/Hermite, `Gamma`, `besselJ` |
| `07-numerics-user-functions.input` | Programming | user functions with `==`, loops, Newton's method at 40 digits, memoised recurrences, an RK4 integrator |
| `08-pde-and-transforms.input` | PDEs | heat and wave equation checks (heat kernel, d'Alembert), `laplace`, Fourier sine coefficients |
| `09-probability.input` | Probability | moments from an MGF, Poisson cumulants, exact dice probabilities, Gaussian integrals, Stirling |
| `10-using-spad.input` + `Quadrature.spad` | Extending the library | a generic SPAD package `SimpleQuadrature(R)` compiled with `)compile` and used over `DoubleFloat` and `Float` |

## Language cheat sheet

| Syntax | Meaning |
|--------|---------|
| `x := expr` | assign (evaluated now) |
| `f(x) == expr` | define a function (evaluated when called; compiled on first use) |
| `fib(n \| n > 1) == ...` | definition guarded by a condition; with base cases this makes a cached recurrence |
| `v : Matrix Float := ...` | declare a type, then assign |
| `expr :: Float` | convert to a domain |
| `op(args)$Domain` | call the version of `op` from a particular domain/package |
| `expr @ Type` | choose the overload that returns `Type` |
| `(a, b) +-> a*b` | anonymous function |
| `[f(i) for i in 1..n \| odd? i]` | list comprehension with a filter |
| `[.. for i in A for j in B]` | **parallel** (zipped) iteration, not nested; nest the brackets to get a product |
| `y := operator 'y` | an undefined function, used to write differential equations |
| `%pi, %e, %i, %plusInfinity` | built-in constants |
| `%` | the previous result |
| `)clear all`, `)read file`, `)compile file.spad` | system commands |

## Pitfalls these files work around

* `free` is a reserved word; don't use it as a variable name.
* Earlier assignments stay in scope: if `w` has been assigned, `cos(w*t)`
  uses that value. Start each topic with `)clear all` or use fresh names.
* `solve` returns `x^2 - 3 = 0` unsolved when the roots are irrational;
  `radicalSolve` writes them out with radicals.
* A definite integral gives back a `Union` (it can come back as `"failed"`),
  so you can't do arithmetic on it directly. For symbolic limits of
  integration, integrate indefinitely and evaluate at the ends (file 08).
* `simplify` and `normalize` clean up trigonometric/exponential identities
  that are left unsimplified by default (file 03, resonance).

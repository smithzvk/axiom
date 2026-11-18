# Applied ACL2: ten industrial-style verification examples

(This directory has nothing to do with Axiom itself; it is a companion to
`../applied-math/`, doing the same exercise for the ACL2 theorem prover.)

ACL2 ("A Computational Logic for Applicative Common Lisp") is a
programming language and a theorem prover in one. You write a model in a
side-effect-free subset of Common Lisp. The same definitions run as
ordinary compiled code (simulators, reference implementations, test
oracles), and you prove theorems about them. Its main industrial use has
been hardware and low-level systems: AMD, Intel, Centaur/VIA, Arm,
Rockwell Collins, Oracle and Kestrel Institute have all used it.

Each book below is a small, self-contained version of one of those uses.
They aren't toys: each proves a property for all inputs, or all widths,
programs or schedules, which testing cannot do. Several also run concrete
examples to show that the model executes.

## Running them

```
sudo apt install acl2 acl2-books acl2-books-certs   # Ubuntu/Debian: ACL2 8.5
./certify.sh                     # certify all ten books (~40 s in total)
./certify.sh 05-separation-kernel   # or just one
```

`certify.sh` runs `(certify-book ...)` on each file with the plain
`acl2` binary and prints `ok`/`FAIL`. The full transcript goes to
`NAME.out`. If a book has a `NAME.acl2` file, the forms in it are run
first, following the `cert.pl` convention, so the books also build with
ACL2's own `make`/`cert.pl` in a source install.

To work interactively, start `acl2` and type
`(ld "04-verified-compiler.lisp")`, or paste forms one at a time. A
failed proof prints "key checkpoints": the simplified goals ACL2 could not
finish, which tell you what lemma is missing.

All ten books certify on ACL2 8.5 (Ubuntu 24.04 package) with the
community books.

## The books

| File | Application area | What is proved | Real-world counterpart |
|------|-----------------|----------------|------------------------|
| `01-adder-multiplier.lisp` | Arithmetic hardware | Gate-level ripple-carry adder, **carry-select adder** and shift-and-add multiplier, correct for **every bit width**; carry-select ≡ ripple for every split point | AMD K5/Athlon FPU, Centaur media unit and Intel/Arm datapath proofs |
| `02-bit-tricks-gl.lisp` | Compilers, C idioms, DSP (with **GL**) | Divide-by-10 and divide-by-7 "magic number" code; the binary-search midpoint overflow bug (a counterexample) and its fix; SWAR popcount; signed-overflow detection; branch-free saturating Q15 add. All exhaustive over 32-bit inputs (2³² to 2⁶⁴ cases) | Centaur's GL-based datapath verification; compiler strength reduction |
| `03-isqrt-loop-invariants.lisp` | Embedded code | A binary-search integer square root: termination, loop invariant, specification, **uniqueness** of the answer, and guard verification | Firmware and DSP code verification |
| `04-verified-compiler.lisp` | Compilers / VMs | Expression compiler to a stack machine with jumps is correct for every program, environment and stack; constant-folding optimizer preserves meaning; the full pipeline is correct | JVM (M1–M6) and x86isa models; AAMP7G code verification |
| `05-separation-kernel.lisp` | Security / avionics | **Noninterference**: for any set of partitions closed under the flow policy, nothing outside it can affect it, for arbitrary (even malicious) application code. Then instantiated, by functional instantiation, for a concrete one-way "data diode" policy | Rockwell Collins AAMP7G separation kernel (MILS) |
| `06-varint-codec.lisp` | Parsers / wire formats | LEB128 (protobuf/WebAssembly/DWARF varint): round trip with trailing data; the lenient decoder is **malleable**; the strict decoder accepts exactly one encoding per value | Kestrel's verified parsers and formats |
| `07-order-matching.lisp` | Finance | Exchange matching engine: no trade-through, price priority, buyer and seller **quantity conservation**, the book stays well-formed, **no crossed book** | Matching-engine and trading-venue verification |
| `08-modexp-crypto.lisp` | Cryptography | Square-and-multiply modular exponentiation tied to `b^e mod m` with **MBE** and guard verification; the RSA multiplicative property; RSA round trip on a 196-bit key and a Fermat check on 2¹²⁷−1, all run inside the logic | Kestrel crypto and zero-knowledge work; MBE as used in industrial ACL2 code |
| `09-railway-interlocking.lisp` | Safety-critical control | No two set routes share track, and every set route's points are locked in position, for **every** sequence of route requests, cancellations and train movements | Railway interlocking (EN 50128); Rockwell Collins mode-logic proofs |
| `10-peterson-mutex.lisp` | Concurrency | Peterson's algorithm guarantees mutual exclusion under **every interleaving**; swapping two lines breaks it, with a concrete failing schedule | Cache-coherence and concurrent-protocol verification |

## ACL2 techniques demonstrated

| Technique | Where |
|-----------|-------|
| Induction over recursive models; induction hints (`:induct`) | 01, 04, 06, 07 |
| Custom induction schemes (a function written only to describe the induction) | 04 (`comp-induct`), 05 (`krun2-induct`), 06 (`encode-induct`) |
| Termination arguments (`:measure`) | 01, 03, 04, 06, 07, 08 |
| Guards and guard verification (no runtime type errors, compiled execution) | 03, 06, 08 |
| `mbe`: proved-equal logic and exec definitions | 08 |
| GL symbolic simulation (exhaustive bit-level proofs, counterexamples) | 02 |
| `encapsulate`: theorems about *unknown* functions (arbitrary code) | 05 |
| `defun-sk` (quantifiers) and functional instantiation | 05 |
| Inductive invariants for reactive systems | 05, 09, 10 |
| Steering the prover: `:use`, `:in-theory`, minimal theories, disabling definitions | 01, 08, 09 |
| Ground evaluation as a test oracle (`defthm` on concrete values) | most books |

## How a failure looks

GL prints concrete counterexamples. Changing the division-by-10 constant
in book 02 from `#xCCCCCCCD` to `#xCCCCCCCC` makes certification fail
with

```
*** SYMBOLIC EXECUTION ERROR ***: Counterexamples found.
...
Counterexample verified.
```

along with specific 32-bit values of `x` where the code is wrong. The
`mid-naive-is-wrong` and `reordered-peterson-is-broken` theorems record
the same kind of finding as a permanent regression check.

## Pitfalls these files work around

* **Name clashes with Common Lisp/ACL2.** `ev`, `pc`, `isqrt` and `fill`
  are taken. ACL2 refuses to define (or `let`-bind) them, so the books
  use `eval-expr`, `pc-of`, `int-sqrt` and `fq`.
* **`arithmetic-5` is powerful but can loop.** In 03 its `(floor x 2)`
  rule turns simple bounds into parity case splits, so it is disabled
  locally. In 08 the library loops on the square-and-multiply step, so the
  step is proved in a minimal theory with explicit `:use` hints. Using a
  private `pow` instead of `expt` keeps the library's `expt` rules out of
  the way.
* **`(mv-nth 0 x)` is printed and rewritten as `(car x)`.** Rules about
  the first value of a multiple-value function must be stated with `car`
  (06).
* **Rules about a function only fire while it is disabled.** If
  `point-pos` or `route-sections` stay enabled they get expanded before the
  lemmas about them can apply (09). The pattern is: prove the lemmas,
  then `(in-theory (disable ...))`.
* **Constant tables get unfolded.** In 09 the prover expanded the route
  table into one case per route until `known-route`, `route-sections` and
  `route-points` were disabled. The safety proof then holds for any
  table, not just this one.
* **Packages must exist before the book is read.** GL's `gl::` symbols
  need `centaur/gl/portcullis` loaded before certification. That is what
  `02-bit-tricks-gl.acl2` does.

## Further reading

* Kaufmann, Manolios, Moore, *Computer-Aided Reasoning: An Approach*
  (the ACL2 textbook) and *Computer-Aided Reasoning: ACL2 Case Studies*.
* The ACL2 home page and XDOC manual: <https://www.cs.utexas.edu/~moore/acl2/>
* Russinoff, *Formal Verification of Floating-Point Hardware Design*
  (Springer, 2019; 2nd ed. 2022) on AMD/Arm FPU proofs.
* Greve, Wilding, Vanfleet, "A Separation Kernel Formal Security Policy"
  (ACL2 Workshop 2003), the GWV policy behind book 05.
* Swords and Davis, "Bit-Blasting ACL2 Theorems" (ACL2 Workshop 2011), on GL.
* Goel, Hunt, Kaufmann, "Engineering a Formal, Executable x86 ISA
  Simulator for Software Verification" (2017).

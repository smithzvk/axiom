; 03  Verifying a loop: integer square root for embedded code
;
; Industry context: Embedded and DSP code computes integer square roots
; for vector lengths, RMS meters and distance checks, often on hardware
; with no floating point.  The classic bugs are off-by-one results at
; perfect squares and overflow in the midpoint, and both are easy to
; miss in testing.  This file shows the ACL2 method for loops:
;
;   1. write the loop as a recursive function and prove that it
;      terminates (ACL2 will not admit a definition until it has done so);
;   2. state the specification without referring to the code;
;   3. prove the loop invariant, then the specification;
;   4. verify the guards, which shows the code never calls a primitive
;      outside its domain and lets it run as compiled Common Lisp.
;
; C code being modelled:
;
;   uint32_t int_sqrt(uint32_t n) {           /* largest r with r*r <= n */
;     uint64_t lo = 0, hi = (uint64_t)n + 1; /* lo*lo <= n < hi*hi     */
;     while (hi - lo > 1) {
;       uint64_t mid = lo + (hi - lo) / 2;
;       if (mid * mid <= n) lo = mid; else hi = mid;
;     }
;     return lo;
;   }

(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)
;; arithmetic-5 would rewrite (floor x 2) into case splits on parity;
;; here the plain bounds on floor are all we need.
(local (in-theory (disable |(floor x 2)|)))

;; The midpoint  lo + (hi - lo)/2 , and the facts the proofs rely on: it
;; is a natural number strictly between lo and hi.  The second fact also
;; shows the midpoint cannot overflow: it never exceeds hi.  (Compare the
;; (lo + hi)/2 overflow in file 02.)
(defun mid (lo hi)
  (declare (xargs :guard (and (integerp lo) (integerp hi))))
  (+ lo (floor (- hi lo) 2)))

(defthm mid-natural
  (implies (and (natp lo) (natp hi) (< lo hi))
           (and (integerp (mid lo hi)) (<= 0 (mid lo hi)))))

(defthm mid-strictly-between
  (implies (and (integerp lo) (integerp hi) (< (+ lo 1) hi))
           (and (< lo (mid lo hi)) (< (mid lo hi) hi)))
  :rule-classes (:rewrite :linear))

(in-theory (disable mid))

;; The loop.  The :measure is the termination argument (the interval
;; shrinks); the :guard says what the inputs must be.
(defun isqrt-loop (n lo hi)
  (declare (xargs :guard (and (natp n) (natp lo) (natp hi) (< lo hi))
                  :measure (nfix (- hi lo))))
  (if (or (not (natp lo)) (not (natp hi)) (<= (- hi lo) 1))
      lo
    (let ((m (mid lo hi)))
      (if (<= (* m m) n)
          (isqrt-loop n m hi)
        (isqrt-loop n lo m)))))

(defun int-sqrt (n)
  (declare (xargs :guard (natp n)))
  (isqrt-loop n 0 (+ n 1)))

;; The specification, which says nothing about how r is found.
(defun isqrt-spec-p (r n)
  (and (natp r)
       (<= (* r r) n)
       (< n (* (+ r 1) (+ r 1)))))

;; The loop invariant  lo^2 <= n < hi^2  survives every iteration, and
;; when the loop exits (hi = lo + 1) it is exactly the specification.
(defthm isqrt-loop-correct
  (implies (and (natp n) (natp lo) (natp hi) (< lo hi)
                (<= (* lo lo) n)
                (< n (* hi hi)))
           (isqrt-spec-p (isqrt-loop n lo hi) n)))

(defthm int-sqrt-correct
  (implies (natp n)
           (isqrt-spec-p (int-sqrt n) n)))

;; The specification determines the answer uniquely, so any other
;; correct implementation (Newton's method, a hardware unit, a lookup
;; table) must return the same value as this one.
(defthm isqrt-spec-unique
  (implies (and (isqrt-spec-p r1 n) (isqrt-spec-p r2 n))
           (equal r1 r2))
  :rule-classes nil
  :hints (("Goal" :cases ((< r1 r2) (< r2 r1)))
          ("Subgoal 2" :nonlinearp t)
          ("Subgoal 1" :nonlinearp t)))

;; It also runs: exact results on bignums, at compiled-code speed.
(defthm int-sqrt-examples
  (and (equal (int-sqrt 0) 0)
       (equal (int-sqrt 15) 3)
       (equal (int-sqrt 16) 4)
       (equal (int-sqrt #xFFFFFFFF) 65535)
       (equal (int-sqrt (expt 10 40)) (expt 10 20)))
  :rule-classes nil)

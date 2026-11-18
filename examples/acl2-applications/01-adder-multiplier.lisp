; 01  Gate-level arithmetic hardware: adders and a multiplier
;
; Industry context: ACL2's best-known use is proving that arithmetic
; hardware is correct.  AMD (K5 and Athlon floating point), Centaur/VIA
; (the Nano media unit), Intel and Arm have all used it this way.  Real
; flows verify RTL that has been translated into ACL2; here the circuits
; are written directly as ACL2 functions over bit lists.
;
; What makes this more than a test bench: the theorems hold for every
; width, not one fixed bus size.  A simulation can only check finitely
; many inputs; these proofs go by induction on the width.
;
; Circuits:
;   * a full adder built from AND/OR/XOR gates
;   * an n-bit ripple-carry adder
;   * a carry-select adder (the faster design: compute the upper half for
;     both possible carries in parallel, then pick one with a mux), proved
;     equal to the ripple adder for every width and every split point
;   * a shift-and-add multiplier built from the adder

(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)

;; ---------------------------------------------------------------------
;; Bits and bit vectors.  A wire is 0 or 1; anything else is read as 0,
;; so the circuit functions need no type hypotheses.  Vectors are lists,
;; least-significant bit first.

(defun bv (x) (if (equal x 1) 1 0))

(defun g-and (a b) (if (and (equal (bv a) 1) (equal (bv b) 1)) 1 0))
(defun g-or  (a b) (if (or  (equal (bv a) 1) (equal (bv b) 1)) 1 0))
(defun g-xor (a b) (if (equal (bv a) (bv b)) 0 1))
(defun g-mux (sel a b) (if (equal (bv sel) 1) a b))   ; 1 -> a, 0 -> b

(defun val (bs)                          ; unsigned value of a vector
  (if (endp bs)
      0
    (+ (bv (car bs)) (* 2 (val (cdr bs))))))

;; ---------------------------------------------------------------------
;; Full adder and ripple-carry adder

(defun fa-sum   (a b c) (g-xor (g-xor a b) c))
(defun fa-carry (a b c) (g-or (g-and a b) (g-and c (g-xor a b))))

(defthm full-adder-correct
  (equal (+ (fa-sum a b c) (* 2 (fa-carry a b c)))
         (+ (bv a) (bv b) (bv c)))
  :rule-classes (:rewrite :linear))

;; From here on we reason about the full adder only through its
;; specification, the way a hierarchical hardware proof treats a cell
;; that has already been verified.

(defthm bv-fa-carry
  (equal (bv (fa-carry a b c)) (fa-carry a b c)))

(defthm bv-fa-sum
  (equal (bv (fa-sum a b c)) (fa-sum a b c)))

(defthm bv-bv (equal (bv (bv x)) (bv x)))

(in-theory (disable fa-sum fa-carry bv))

;; Adds two vectors of any (possibly different) lengths; the result has
;; one more bit than the longer input (the carry out).
(defun ripple-add (as bs c)
  (declare (xargs :measure (+ (len as) (len bs))))
  (if (and (endp as) (endp bs))
      (list (bv c))
    (cons (fa-sum (car as) (car bs) c)
          (ripple-add (cdr as) (cdr bs) (fa-carry (car as) (car bs) c)))))

(defthm ripple-add-correct
  (equal (val (ripple-add as bs c))
         (+ (val as) (val bs) (bv c)))
  :hints (("Goal" :induct (ripple-add as bs c))))

(defthm len-ripple-add
  (equal (len (ripple-add as bs c))
         (+ 1 (max (len as) (len bs))))
  :hints (("Goal" :induct (ripple-add as bs c))))

;; ---------------------------------------------------------------------
;; Carry-select adder.  Split both operands at bit K.  The low half goes
;; through a ripple adder.  The high half is added twice, with carry-in
;; 0 and with carry-in 1, at the same time as the low half; the low
;; half's carry-out then picks which high result to use.

(defun mux-list (sel xs ys)
  (declare (xargs :measure (+ (len xs) (len ys))))
  (if (and (endp xs) (endp ys))
      nil
    (cons (g-mux sel (car xs) (car ys))
          (mux-list sel (cdr xs) (cdr ys)))))

(defun csel-add (k as bs c)
  (let* ((lo    (ripple-add (take k as) (take k bs) c)) ; k+1 bits
         (cout  (nth k lo))
         (hi0   (ripple-add (nthcdr k as) (nthcdr k bs) 0))
         (hi1   (ripple-add (nthcdr k as) (nthcdr k bs) 1)))
    (append (take k lo) (mux-list cout hi1 hi0))))

;; Lemmas: how VAL behaves on the list operations used above
(defthm val-append
  (equal (val (append xs ys))
         (+ (val xs) (* (expt 2 (len xs)) (val ys)))))

(defthm val-mux-list
  (equal (val (mux-list sel xs ys))
         (if (equal (bv sel) 1) (val xs) (val ys)))
  :hints (("Goal" :induct (mux-list sel xs ys))))

(defthm val-take-of-nil
  (equal (val (take k nil)) 0))

(defthm nthcdr-of-nil
  (equal (nthcdr k nil) nil))

(defthm val-take-plus-nthcdr
  (implies (natp k)
           (equal (+ (val (take k xs)) (* (expt 2 k) (val (nthcdr k xs))))
                  (val xs)))
  :rule-classes nil)

(defthm bv-of-nth-carry
  ;; The top bit of a k-bit addition is the carry: val = low k bits
  ;; plus 2^k times bit k.
  (implies (and (natp k) (equal (len xs) (+ 1 k)))
           (equal (val xs)
                  (+ (val (take k xs)) (* (expt 2 k) (bv (nth k xs))))))
  :rule-classes nil)

(defthm len-take-for-csel
  (equal (len (take k xs)) (nfix k)))

(defthm csel-add-correct
  (implies (natp k)
           (equal (val (csel-add k as bs c))
                  (+ (val as) (val bs) (bv c))))
  :hints (("Goal"
           :in-theory (disable take nthcdr nth)
           :use ((:instance val-take-plus-nthcdr (xs as))
                 (:instance val-take-plus-nthcdr (xs bs))
                 (:instance bv-of-nth-carry
                            (xs (ripple-add (take k as) (take k bs) c)))))))

;; The design-level equivalence a hardware team cares about: swapping the
;; slow adder for the fast one never changes the answer, whatever the
;; width and wherever the split is made.
(defthm csel-equivalent-to-ripple
  (implies (natp k)
           (equal (val (csel-add k as bs c))
                  (val (ripple-add as bs c))))
  :hints (("Goal" :in-theory (disable csel-add ripple-add))))

;; ---------------------------------------------------------------------
;; Shift-and-add multiplier: for each multiplier bit, add the
;; multiplicand (or zero) to the partial product shifted left by one.

(defun mult (as bs)
  (if (endp as)
      nil
    (ripple-add (if (equal (bv (car as)) 1) bs nil)
                (cons 0 (mult (cdr as) bs))
                0)))

(defthm mult-correct
  (equal (val (mult as bs))
         (* (val as) (val bs))))

;; The definitions also execute, so the same model can serve as a
;; reference simulator: 13 * 11 = 143.
(defthm mult-example
  (equal (val (mult '(1 0 1 1) '(1 1 0 1))) 143)
  :rule-classes nil)

; 08  Cryptographic arithmetic: fast modular exponentiation, with the
;     fast code tied to its specification via MBE
;
; Industry context: ACL2 is used to verify cryptographic code.  Kestrel
; Institute's work on elliptic-curve and zero-knowledge circuits (e.g.
; for Zcash and Aleo) is one example, and floating-point and big-number
; hardware such as Arm's have been verified the same way.  The pattern
; shown here is MBE ("must be equal"), which industrial ACL2 code uses
; everywhere:
;
;     (mbe :logic <obviously-correct spec>  :exec <fast implementation>)
;
; The prover reasons about the :logic form.  When the code runs it uses
; the :exec form.  Guard verification proves once that the two are equal
; on every legal input, so nobody has to trust the fast code separately.
;
; Here the spec is (b^e mod m), which is hopeless to compute directly for
; RSA-sized exponents, and the implementation is right-to-left
; square-and-multiply.  At the end, both are used to run textbook RSA on
; bignums inside the logic.

(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)

;; ---------------------------------------------------------------------
;; Implementation: square-and-multiply with accumulator ACC.
;; Invariant: ACC * B^E mod M is the same in every iteration.

(defun modexp-loop (b e m acc)
  (declare (xargs :guard (and (natp b) (natp e) (posp m) (natp acc))
                  :measure (nfix e)))
  (if (zp e)
      (mod acc m)
    (modexp-loop (mod (* b b) m)
                 (floor e 2)
                 m
                 (if (oddp e) (mod (* acc b) m) acc))))

;; The exponent function used in the specification.  It is ACL2's
;; built-in EXPT on natural exponents; a separate definition keeps the
;; library's many EXPT rewrite rules out of the way.
(defun pow (b e)
  (declare (xargs :guard (and (natp b) (natp e))))
  (if (zp e) 1 (* b (pow b (1- e)))))

(defthm pow-is-expt
  (implies (natp e) (equal (pow b e) (expt b e)))
  :rule-classes nil)

(defthm natp-pow
  (implies (natp b) (natp (pow b e)))
  :rule-classes :type-prescription)

;; Algebra used by the proof: reducing mod m before exponentiating does
;; not change the result, and b^e = (b^2)^(e/2) * b^(e mod 2).
(defthm mod-pow-mod
  (implies (and (natp b) (posp m))
           (equal (mod (pow (mod b m) e) m)
                  (mod (pow b e) m))))

(defthm pow-square-half
  (implies (and (natp b) (natp e))
           (equal (pow b e)
                  (* (pow (* b b) (floor e 2))
                     (if (oddp e) b 1))))
  :rule-classes nil)

(defthm mod-times-mod-pow
  (implies (and (natp x) (natp b) (posp m))
           (equal (mod (* x (pow (mod b m) k)) m)
                  (mod (* x (pow b k)) m)))
  :hints (("Goal"
           :in-theory (disable mod-pow-mod pow)
           :use ((:instance mod-pow-mod (e k))
                 (:instance (:theorem
                             (implies (and (natp x) (natp y) (posp m))
                                      (equal (mod (* x (mod y m)) m)
                                             (mod (* x y) m))))
                            (y (pow (mod b m) k)))
                 (:instance (:theorem
                             (implies (and (natp x) (natp y) (posp m))
                                      (equal (mod (* x (mod y m)) m)
                                             (mod (* x y) m))))
                            (y (pow b k)))))))

(defthm mod-acc-lemma
  (implies (and (natp acc) (natp b) (natp p) (posp m))
           (equal (mod (* (mod (* acc b) m) p) m)
                  (mod (* acc (* p b)) m))))

;; One loop iteration preserves  acc * b^e mod m , for odd and even e.
(defthm modexp-step-odd
  (implies (and (natp b) (natp e) (oddp e) (posp m) (natp acc))
           (equal (mod (* (mod (* acc b) m) (pow (* b b) (floor e 2))) m)
                  (mod (* acc (pow b e)) m)))
  :hints (("Goal" :in-theory (disable pow oddp mod-acc-lemma)
                  :use (pow-square-half
                        (:instance mod-acc-lemma
                                   (p (pow (* b b) (floor e 2))))))))

(defthm modexp-step-even
  (implies (and (natp b) (natp e) (not (oddp e)) (posp m) (natp acc))
           (equal (mod (* acc (pow (* b b) (floor e 2))) m)
                  (mod (* acc (pow b e)) m)))
  :hints (("Goal" :in-theory (disable pow oddp)
                  :use (pow-square-half))))

(defthm natp-mod-for-loop
  (implies (and (natp x) (posp m)) (natp (mod x m)))
  :rule-classes :type-prescription)

(defthm natp-floor-for-loop
  (implies (natp e) (natp (floor e 2)))
  :rule-classes :type-prescription)

;; The loop theorem.  The arithmetic library on its own goes into a
;; rewriting loop on this goal, so the inductive step is done in a
;; minimal theory, using only the lemmas above.  Steering the prover
;; like this is routine in industrial ACL2 work.
(defthm modexp-loop-correct
  (implies (and (natp b) (natp e) (posp m) (natp acc))
           (equal (modexp-loop b e m acc)
                  (mod (* acc (pow b e)) m)))
  :hints (("Goal" :induct (modexp-loop b e m acc))
          ("Subgoal *1/2"
           :in-theory (union-theories '(natp-mod-for-loop natp-floor-for-loop
                                        natp-pow posp natp zp
                                        natp-compound-recognizer
                                        posp-compound-recognizer)
                                      (theory 'minimal-theory))
           :expand ((modexp-loop b e m acc))
           :cases ((oddp e))
           :use ((:instance mod-times-mod-pow
                            (x (if (oddp e) (mod (* acc b) m) acc))
                            (b (* b b)) (k (floor e 2)))
                 modexp-step-odd modexp-step-even
                 (:instance natp-mod-for-loop (x (* acc b)))
                 (:instance natp-mod-for-loop (x (* b b)))
                 natp-floor-for-loop))))

;; ---------------------------------------------------------------------
;; The public function.  Logically it is the specification; in execution
;; it is the loop.  VERIFY-GUARDS proves the two agree.

(defun modexp (b e m)
  (declare (xargs :guard (and (natp b) (natp e) (posp m))
                  :verify-guards nil))
  (mbe :logic (mod (pow b e) m)
       :exec  (modexp-loop (mod b m) e m 1)))

(verify-guards modexp)

;; Properties are proved about the clean specification and apply to the
;; fast code automatically.  Example: the multiplicative property that
;; makes RSA signatures homomorphic (and blinding attacks possible).
(defthm modexp-multiplicative
  (implies (and (natp a) (natp b) (natp e) (posp m))
           (equal (modexp (* a b) e m)
                  (mod (* (modexp a e m) (modexp b e m)) m))))

;; ---------------------------------------------------------------------
;; Executing it: RSA with two Mersenne primes (2^89 - 1 and 2^107 - 1),
;; giving a 196-bit modulus.  Too small to be secure, but every number is
;; a bignum, and the theorems below are proved by running the guarded
;; code; computing the spec's 2^196-sized power directly would never
;; finish.

(defun egcd-inv (a b x0 x1)       ; extended Euclid; returns a^-1 mod b0
  (declare (xargs :measure (nfix b)
                  :guard (and (natp a) (natp b) (integerp x0) (integerp x1))))
  (if (zp b)
      (ifix x0)
    (egcd-inv b (mod a b) x1 (- x0 (* (floor a b) x1)))))

(defun mod-inverse (a m)
  (declare (xargs :guard (and (natp a) (posp m))))
  (mod (egcd-inv a m 1 0) m))

(defconst *p* (- (expt 2 89) 1))
(defconst *q* (- (expt 2 107) 1))
(defconst *n* (* *p* *q*))
(defconst *e* 65537)
(defconst *d* (mod-inverse *e* (* (- *p* 1) (- *q* 1))))

(defun rsa-encrypt (msg) (declare (xargs :guard (natp msg))) (modexp msg *e* *n*))
(defun rsa-decrypt (c)   (declare (xargs :guard (natp c)))   (modexp c *d* *n*))

(defthm rsa-key-is-consistent
  (equal (mod (* *e* *d*) (* (- *p* 1) (- *q* 1))) 1)
  :rule-classes nil)

(defthm rsa-roundtrip-example
  (let ((msg 123456789012345678901234567890))
    (and (not (equal (rsa-encrypt msg) msg))
         (equal (rsa-decrypt (rsa-encrypt msg)) msg)))
  :rule-classes nil)

;; Fermat test on a 127-bit prime: 3^(p-1) = 1 (mod p) for p = 2^127 - 1.
(defthm fermat-check-m127
  (equal (modexp 3 (- (expt 2 127) 2) (- (expt 2 127) 1)) 1)
  :rule-classes nil)

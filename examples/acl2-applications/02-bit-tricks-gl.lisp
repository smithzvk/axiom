; 02  Bit-level code: compiler tricks and low-level C idioms, checked
;     exhaustively with GL symbolic simulation
;
; Industry context: Centaur Technology used GL (built on ACL2 by Sol
; Swords and Jared Davis) to verify the floating-point and media units
; of its x86 processors; the same machinery checks microcode and the
; bit-twiddling found in compilers, codecs and crypto libraries.
;
; GL proves a theorem about fixed-width values by symbolically simulating
; the ACL2 definitions over BDDs (or, with a SAT backend, AIGs).  For a
; 32-bit input that covers all 4,294,967,296 cases at once, and when a
; property is false GL prints a concrete counterexample.  The proof is
; checked by ACL2 itself, so the result is a theorem, not a test.
;
; Each function below is a transliteration of the C expression in its
; comment, with unsigned 32-bit wraparound made explicit.

(in-package "ACL2")
(include-book "centaur/gl/gl" :dir :system)

(defmacro u32 (x) `(logand ,x #xFFFFFFFF))     ; C's uint32_t wraparound

;; ---------------------------------------------------------------------
;; 1. Division by a constant.  Compilers replace x / 10 by a multiply and
;;    a shift (division is 20-40 cycles, a multiply 3).  The "magic
;;    number" is easy to get wrong by one; this proves it for all x.
;;      uint32_t q = (uint64_t)x * 0xCCCCCCCD >> 35;

(defun div10-fast (x) (ash (* x #xCCCCCCCD) -35))

(gl::def-gl-thm div10-fast-correct
  :hyp   (unsigned-byte-p 32 x)
  :concl (equal (div10-fast x) (floor x 10))
  :g-bindings (gl::auto-bindings (:nat x 32)))

;; Dividing by 7 needs a 33-bit multiplier, so compilers emit an extra
;; "add and shift" fix-up step (Granlund & Montgomery, 1994):
;;      uint32_t q = (uint64_t)x * 0x24924925 >> 32;
;;      uint32_t t = ((x - q) >> 1) + q;
;;      return t >> 2;

(defun div7-fast (x)
  (let* ((q (ash (* x #x24924925) -32))
         (s (+ (ash (u32 (- x q)) -1) q)))
    (ash (u32 s) -2)))

(gl::def-gl-thm div7-fast-correct
  :hyp   (unsigned-byte-p 32 x)
  :concl (equal (div7-fast x) (floor x 7))
  :g-bindings (gl::auto-bindings (:nat x 32)))

;; ---------------------------------------------------------------------
;; 2. The binary-search midpoint bug.  For years the JDK (and many
;;    textbooks) used  mid = (lo + hi) / 2 , which overflows when the sum
;;    passes 2^32 (in Java, 2^31).  First the bug, as a theorem with a
;;    concrete witness:

(defun mid-naive (a b) (ash (u32 (+ a b)) -1))

(defthm mid-naive-is-wrong
  (not (equal (mid-naive #xF0000000 #xF0000002)
              (floor (+ #xF0000000 #xF0000002) 2)))
  :rule-classes nil)

;; ...and the overflow-free idiom  (a & b) + ((a ^ b) >> 1) , proved
;; correct for all pairs of 32-bit inputs (2^64 cases):

(defun mid-safe (a b) (+ (logand a b) (ash (logxor a b) -1)))

(gl::def-gl-thm mid-safe-correct
  :hyp   (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
  :concl (and (equal (mid-safe a b) (floor (+ a b) 2))
              (unsigned-byte-p 32 (mid-safe a b)))   ; never overflows
  :g-bindings (gl::auto-bindings (:mix (:nat a 32) (:nat b 32))))

;; ---------------------------------------------------------------------
;; 3. Population count without a loop (the "SWAR" algorithm used by
;;    compilers when the CPU has no POPCNT instruction):
;;      x = x - ((x >> 1) & 0x55555555);
;;      x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
;;      x = (x + (x >> 4)) & 0x0F0F0F0F;
;;      return (x * 0x01010101) >> 24;
;;    Specification: LOGCOUNT, ACL2's built-in count of 1 bits.

(defun popcount-swar (x)
  (let* ((x (u32 (- x (logand (ash x -1) #x55555555))))
         (x (+ (logand x #x33333333) (logand (ash x -2) #x33333333)))
         (x (logand (+ x (ash x -4)) #x0F0F0F0F)))
    (ash (u32 (* x #x01010101)) -24)))

(gl::def-gl-thm popcount-swar-correct
  :hyp   (unsigned-byte-p 32 x)
  :concl (equal (popcount-swar x) (logcount x))
  :g-bindings (gl::auto-bindings (:nat x 32)))

;; ---------------------------------------------------------------------
;; 4. Detecting signed overflow after the fact.  Signed overflow is
;;    undefined behaviour in C, so security-sensitive code adds the
;;    unsigned bit patterns and tests the sign bits:
;;      uint32_t s = a + b;
;;      overflow = ((a ^ s) & (b ^ s)) >> 31;
;;    Specification: the true sum of the two's-complement values does not
;;    fit in a signed 32-bit integer.

(defun s32 (x)                         ; read a bit pattern as int32_t
  (if (logbitp 31 x) (- x (expt 2 32)) x))

(defun add-overflows (a b)
  (let ((s (u32 (+ a b))))
    (logbitp 31 (logand (logxor a s) (logxor b s)))))

(gl::def-gl-thm add-overflow-check-correct
  :hyp   (and (unsigned-byte-p 32 a) (unsigned-byte-p 32 b))
  :concl (iff (add-overflows a b)
              (not (signed-byte-p 32 (+ (s32 a) (s32 b)))))
  :g-bindings (gl::auto-bindings (:mix (:nat a 32) (:nat b 32))))

;; ---------------------------------------------------------------------
;; 5. Saturating fixed-point addition, as in DSP code and audio mixing:
;;    Q15 samples are int16_t; the sum is clamped instead of wrapping.
;;    The branch-free version below is checked against the obvious
;;    clamped specification.
;;      int32_t s = a + b;               /* cannot overflow in 32 bits */
;;      int32_t hi = (s - 32767) >> 31;  /* all ones if s <  32767     */
;;      int32_t lo = (s + 32768) >> 31;  /* all ones if s < -32768     */
;;      s = (s & hi) | (32767 & ~hi);
;;      s = (s & ~lo) | (-32768 & lo);

(defun sat-add-q15 (a b)
  (let* ((s  (+ a b))
         (hi (ash (- s 32767) -31))
         (lo (ash (+ s 32768) -31))
         (s  (logior (logand s hi) (logand 32767 (lognot hi)))))
    (logior (logand s (lognot lo)) (logand -32768 lo))))

(defun clamp (lo x hi) (if (< x lo) lo (if (< hi x) hi x)))

(gl::def-gl-thm sat-add-q15-correct
  :hyp   (and (signed-byte-p 16 a) (signed-byte-p 16 b))
  :concl (equal (sat-add-q15 a b) (clamp -32768 (+ a b) 32767))
  :g-bindings (gl::auto-bindings (:mix (:int a 16) (:int b 16))))

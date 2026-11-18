; 06  A binary wire format: verified LEB128 / protobuf varint codec
;
; Industry context: parsers for untrusted input are a leading source of
; security bugs.  Kestrel Institute uses ACL2 for verified parsers and
; formats (including its ABNF grammar tools and the cryptographic formats
; used by blockchain clients), and AWS and others apply the same proof
; patterns to serialization code.
;
; Unsigned LEB128 ("varint") stores 7 bits per byte, least significant
; group first, with the top bit of each byte meaning "more bytes follow".
; It is used by Protocol Buffers, WebAssembly, DWARF debug info and
; Android DEX files.  Example: 300 = #b10 0101100 is encoded as #xAC #x02.
;
; Proved here:
;   * every encoded byte is in 0..255;
;   * round trip: decoding encode(n) followed by ANY trailing bytes gives
;     back n and exactly those trailing bytes (so varints can be
;     concatenated inside a larger message);
;   * the lenient decoder accepts non-minimal encodings (#x80 #x00 also
;     means 0).  That kind of malleability has led to signature and
;     cache-key bugs in practice.  A strict decoder rejects them, and we
;     prove that each value then has exactly one accepted encoding;
;   * all functions are guard-verified, so they run as compiled Lisp.

(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)

(defun bytep (b) (declare (xargs :guard t)) (and (natp b) (< b 256)))

(defun byte-listp (bs)
  (declare (xargs :guard t))
  (if (atom bs) (null bs) (and (bytep (car bs)) (byte-listp (cdr bs)))))

;; ---------------------------------------------------------------------
;; Encoder

(defun encode-varint (n)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (or (zp n) (< n 128))
      (list (nfix n))
    (cons (+ 128 (mod n 128))
          (encode-varint (floor n 128)))))

(defthm byte-listp-encode-varint
  (byte-listp (encode-varint n)))

;; ---------------------------------------------------------------------
;; Lenient decoder (what many hand-written parsers do).
;; Returns (mv value remaining-bytes ok).

(defun decode-varint (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (cond ((atom bytes) (mv 0 nil nil))
        ((< (nfix (car bytes)) 128) (mv (nfix (car bytes)) (cdr bytes) t))
        (t (mv-let (n rest ok)
               (decode-varint (cdr bytes))
             (mv (+ (- (nfix (car bytes)) 128) (* 128 n)) rest ok)))))

(defthm decode-encode-roundtrip
  (implies (natp n)
           (equal (decode-varint (append (encode-varint n) rest))
                  (mv n rest t))))

;; Two different byte strings that the lenient decoder maps to the same
;; value: the malleability problem.
(defthm lenient-decoder-is-malleable
  (and (equal (decode-varint '(0))       (mv 0 nil t))
       (equal (decode-varint '(128 0))   (mv 0 nil t))
       (equal (decode-varint '(172 130 0)) (decode-varint '(172 2))))
  :rule-classes nil)

;; ---------------------------------------------------------------------
;; Strict decoder: a final byte of 0 is only allowed as the whole
;; encoding of 0 (FIRST is true for the first byte), and every byte must
;; be in range.

(defun decode-strict (bytes first)
  (declare (xargs :guard t))
  (cond ((atom bytes) (mv 0 nil nil))
        ((not (bytep (car bytes))) (mv 0 nil nil))
        ((< (car bytes) 128)
         (if (and (equal (car bytes) 0) (not first))
             (mv 0 nil nil)                       ; non-minimal: reject
           (mv (car bytes) (cdr bytes) t)))
        (t (mv-let (n rest ok)
               (decode-strict (cdr bytes) nil)
             (if ok
                 (mv (+ (- (car bytes) 128) (* 128 n)) rest t)
               (mv 0 nil nil))))))

;; (ACL2 writes (mv-nth 0 x) as (car x), so these facts about the
;; returned value are stated with CAR.)
(defthm decode-strict-continuation-is-positive
  (implies (mv-nth 2 (decode-strict bytes nil))
           (< 0 (car (decode-strict bytes nil))))
  :rule-classes :linear)

(defthm natp-decode-strict
  (natp (car (decode-strict bytes first)))
  :rule-classes :type-prescription)

;; Round trip for the strict decoder: every encoder output is accepted.
;; The induction follows the encoder, with FIRST becoming NIL after the
;; first byte.
(defun encode-induct (n first)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (< n 128))
      first
    (encode-induct (floor n 128) nil)))

(defthm decode-strict-encode
  (implies (and (natp n) (or first (< 0 n)))
           (equal (decode-strict (append (encode-varint n) rest) first)
                  (mv n rest t)))
  :hints (("Goal" :induct (encode-induct n first))))

;; One byte of the encoding: a continuation byte b followed by the
;; encoding of a positive n.
(defthm encode-varint-step
  (implies (and (natp b) (<= 128 b) (< b 256) (natp n) (< 0 n))
           (equal (encode-varint (+ -128 b (* 128 n)))
                  (cons b (encode-varint n)))))

;; Uniqueness: whatever the strict decoder accepts is exactly the
;; canonical encoding of the value it returns, followed by the rest.  So
;; each value has one accepted byte string, and re-encoding a parsed
;; message reproduces the input bit for bit.
(defthm decode-strict-only-accepts-canonical
  (implies (mv-nth 2 (decode-strict bytes first))
           (equal (append (encode-varint (mv-nth 0 (decode-strict bytes first)))
                          (mv-nth 1 (decode-strict bytes first)))
                  bytes))
  :hints (("Goal" :in-theory (disable encode-varint)
                  :expand ((encode-varint (car bytes))))))

(defthm strict-decoder-examples
  (and (equal (encode-varint 300) '(#xAC #x02))
       (equal (decode-strict '(#xAC #x02 #x07) t) (mv 300 '(7) t))
       (equal (mv-nth 2 (decode-strict '(128 0) t)) nil)        ; rejected
       (equal (encode-varint (expt 2 64)) '(128 128 128 128 128 128 128 128 128 2)))
  :rule-classes nil)

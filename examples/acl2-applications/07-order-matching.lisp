; 07  Financial systems: invariants of an exchange matching engine
;
; Industry context: exchanges and trading firms run matching engines whose
; failures cost money directly: trading through a better price, losing or
; creating quantity, leaving a crossed book.  Formal methods are used in
; this sector (Imandra, whose prover descends from the Boyer-Moore
; tradition that ACL2 belongs to, is used to model trading venues), and
; ACL2 is well suited to it: the model is ordinary executable code and the
; regulatory rules become theorems about it.
;
; Model: the resting sell orders (asks) are a list of (price . qty) with
; positive quantities, sorted from best (lowest) price.  An incoming buy
; limit order for QTY at price LIMIT is matched against the best asks.
; The result is the list of fills, the unfilled quantity, and the new
; book.  Proved, for every book and every order:
;
;   1. no trade-through: every fill is at a price <= the buyer's limit;
;   2. price priority: fills happen best price first;
;   3. conservation for the buyer: filled + unfilled = ordered;
;   4. conservation for sellers: quantity removed from the book equals
;      quantity filled, so nothing is created or lost;
;   5. the book stays well-formed (sorted, positive quantities);
;   6. no crossed market: if part of the order is left unfilled, every
;      remaining ask is above the limit, so the remainder can rest as a
;      bid without crossing the book.

(in-package "ACL2")

(defun price (o) (nfix (car o)))
(defun qty   (o) (nfix (cdr o)))

(defun valid-asks (asks)            ; positive quantities, ascending prices
  (if (atom asks)
      (null asks)
    (and (consp (car asks))
         (natp (car (car asks)))
         (posp (cdr (car asks)))
         (or (atom (cdr asks))
             (<= (price (car asks)) (price (cadr asks))))
         (valid-asks (cdr asks)))))

(defun total-qty (os)
  (if (atom os) 0 (+ (qty (car os)) (total-qty (cdr os)))))

;; ---------------------------------------------------------------------
;; Matching

(defun match-buy (limit q asks)
  (declare (xargs :measure (+ (nfix q) (len asks))))
  (cond ((zp q) (mv nil 0 asks))
        ((atom asks) (mv nil q asks))
        ((< (nfix limit) (price (car asks))) (mv nil q asks)) ; too expensive
        (t (let* ((p    (price (car asks)))
                  (aq   (qty (car asks)))
                  (fq (min q aq))
                  (book (if (< fq aq)
                            (cons (cons p (- aq fq)) (cdr asks)) ; partial
                          (cdr asks))))                            ; consumed
             (mv-let (fills rem book2)
                 (match-buy limit (- q fq) book)
               (mv (cons (cons p fq) fills) rem book2))))))

;; ---------------------------------------------------------------------
;; Properties of the fills

(defun all-at-or-below (limit fills)
  (if (atom fills)
      t
    (and (<= (price (car fills)) (nfix limit))
         (all-at-or-below limit (cdr fills)))))

(defun nondecreasing-prices (fills)
  (if (or (atom fills) (atom (cdr fills)))
      t
    (and (<= (price (car fills)) (price (cadr fills)))
         (nondecreasing-prices (cdr fills)))))

(defthm 1-no-trade-through
  (all-at-or-below limit (mv-nth 0 (match-buy limit q asks))))

;; Every fill price is at least the price of the best ask we started from.
(defun all-at-or-above (lo fills)
  (if (atom fills)
      t
    (and (<= lo (price (car fills)))
         (all-at-or-above lo (cdr fills)))))

(defthm fills-at-or-above-best-ask
  (implies (and (valid-asks asks) (consp asks) (<= lo (price (car asks))))
           (all-at-or-above lo (mv-nth 0 (match-buy limit q asks)))))

(defthm all-at-or-above-implies-first
  (implies (and (all-at-or-above lo fills) (consp fills))
           (<= lo (price (car fills))))
  :rule-classes :linear)

(defthm 2-price-priority
  (implies (valid-asks asks)
           (nondecreasing-prices (mv-nth 0 (match-buy limit q asks))))
  :hints (("Goal" :induct (match-buy limit q asks))
          ("Subgoal *1/4"
           :use ((:instance fills-at-or-above-best-ask
                            (lo (price (car asks)))
                            (q (- q (min q (qty (car asks)))))
                            (asks (if (< q (qty (car asks)))
                                      (cons (cons (price (car asks))
                                                  (- (qty (car asks)) q))
                                            (cdr asks))
                                    (cdr asks))))))))

(defthm 3-buyer-conservation
  (implies (natp q)
           (equal (+ (total-qty (mv-nth 0 (match-buy limit q asks)))
                     (mv-nth 1 (match-buy limit q asks)))
                  q)))

(defthm 4-seller-conservation
  (equal (+ (total-qty (mv-nth 0 (match-buy limit q asks)))
            (total-qty (mv-nth 2 (match-buy limit q asks))))
         (total-qty asks)))

(defthm 5-book-stays-valid
  (implies (valid-asks asks)
           (valid-asks (mv-nth 2 (match-buy limit q asks)))))

(defthm 6-no-crossed-book
  (implies (and (valid-asks asks)
                (< 0 (mv-nth 1 (match-buy limit q asks)))
                (consp (mv-nth 2 (match-buy limit q asks))))
           (< (nfix limit) (price (car (mv-nth 2 (match-buy limit q asks)))))))

;; ---------------------------------------------------------------------
;; It is also the executable reference implementation.  A buy of 250 at
;; limit 101 against asks 100x100, 101x100, 101x50, 102x500:
(defthm match-example
  (equal (match-buy 101 250 '((100 . 100) (101 . 100) (101 . 50) (102 . 500)))
         (mv '((100 . 100) (101 . 100) (101 . 50))
             0
             '((102 . 500))))
  :rule-classes nil)

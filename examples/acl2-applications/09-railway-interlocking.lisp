; 09  Safety-critical control: a railway interlocking
;
; Industry context: railway signalling is among the most formally
; verified kinds of software.  Siemens, Alstom and Thales use the B
; method, SAT-based model checking and theorem proving for
; interlockings, and CENELEC EN 50128 recommends formal methods at the
; top safety level.  The same pattern (a controller, an environment that
; can do anything, and a safety invariant proved for every possible
; sequence of events) covers avionics mode logic, which Rockwell Collins
; verified in ACL2, as well as medical devices and industrial PLCs.
;
; The model.  A junction has track sections and points (switches).  A
; ROUTE is a path through the junction: the sections it occupies and the
; position each of its points must be in.  The signaller can request or
; cancel any route, and trains can occupy or clear any section, in any
; order and as often as they like.  The interlocking grants a request
; only if
;   * no section of the route is reserved by another set route,
;   * no section of the route is occupied by a train, and
;   * every point it needs can be moved (points under a set route are
;     locked).
; It then moves and locks the points and clears the signal.
;
; Safety theorem: in every state reachable from the initial state, under
; every command sequence,
;   (a) no two set routes share a track section (no collisions), and
;   (b) every point used by a set route is in the position that route
;       needs (no derailment).
; The proof is a single inductive invariant, which is how such proofs
; scale to real interlocking tables.  Nothing in it depends on the
; particular table, which is just data.

(in-package "ACL2")

;; ---------------------------------------------------------------------
;; Interlocking table for a double junction with crossover.
;; (route-name (sections ...) ((point . position) ...))

(defconst *routes*
  '((r1 (t1 t2 t3)    ((p1 . normal)))
    (r2 (t1 t2 t5)    ((p1 . reverse) (p2 . normal)))
    (r3 (t4 t5 t6)    ((p2 . normal)))
    (r4 (t4 t5 t2 t3) ((p2 . reverse) (p1 . reverse)))
    (r5 (t7 t6)       ((p3 . normal)))
    (r6 (t7 t8)       ((p3 . reverse)))))

(defun known-route (r) (consp (assoc-eq r *routes*)))
(defun route-sections (r) (cadr (assoc-eq r *routes*)))
(defun route-points   (r) (caddr (assoc-eq r *routes*)))

;; ---------------------------------------------------------------------
;; State: set routes, point positions, occupied sections.

(defun mk-st (set points occ) (list set points occ))
(defun st-set    (st) (car st))
(defun st-points (st) (cadr st))
(defun st-occ    (st) (caddr st))

(defun point-pos (p points) (cdr (assoc-eq p points)))

(defun sections-of (routes)               ; all sections reserved by ROUTES
  (if (atom routes)
      nil
    (append (route-sections (car routes)) (sections-of (cdr routes)))))

(defun points-of (routes)                 ; all points locked by ROUTES
  (if (atom routes)
      nil
    (append (strip-cars (route-points (car routes)))
            (points-of (cdr routes)))))

;; Can the required point settings be achieved?  Yes if each point is
;; already in place, or is not locked by a set route.
(defun points-available (need points locked)
  (if (atom need)
      t
    (and (or (equal (point-pos (caar need) points) (cdar need))
             (not (member-eq (caar need) locked)))
         (points-available (cdr need) points locked))))

(defun set-points (need points)
  (if (atom need)
      points
    (acons (caar need) (cdar need) (set-points (cdr need) points))))

;; ---------------------------------------------------------------------
;; Controller.  Commands: (request r), (cancel r), (occupy s), (clear s).

(defun grantable (r st)
  (and (known-route r)
       (not (member-eq r (st-set st)))
       (not (intersectp-eq (route-sections r) (sections-of (st-set st))))
       (not (intersectp-eq (route-sections r) (st-occ st)))
       (points-available (route-points r) (st-points st)
                         (points-of (st-set st)))))

(defun step-ilk (cmd st)
  (let ((op (car cmd)) (x (cadr cmd)))
    (case op
      (request (if (grantable x st)
                   (mk-st (cons x (st-set st))
                          (set-points (route-points x) (st-points st))
                          (st-occ st))
                 st))
      (cancel  (mk-st (remove1-eq x (st-set st)) (st-points st) (st-occ st)))
      (occupy  (mk-st (st-set st) (st-points st) (cons x (st-occ st))))
      (clear   (mk-st (st-set st) (st-points st) (remove-eq x (st-occ st))))
      (otherwise st))))

(defun run-ilk (cmds st)
  (if (atom cmds) st (run-ilk (cdr cmds) (step-ilk (car cmds) st))))

(defconst *init* (mk-st nil nil nil))

;; ---------------------------------------------------------------------
;; Safety properties

;; (a) set routes reserve pairwise disjoint sections (and are distinct)
(defun disjoint-routes (routes)
  (if (atom routes)
      t
    (and (not (member-eq (car routes) (cdr routes)))
         (not (intersectp-eq (route-sections (car routes))
                             (sections-of (cdr routes))))
         (disjoint-routes (cdr routes)))))

;; (b) every point of every set route is in the required position
(defun points-correct (need points)
  (if (atom need)
      t
    (and (equal (point-pos (caar need) points) (cdar need))
         (points-correct (cdr need) points))))

(defun all-points-correct (routes points)
  (if (atom routes)
      t
    (and (points-correct (route-points (car routes)) points)
         (all-points-correct (cdr routes) points))))

(defun safe (st)
  (and (disjoint-routes (st-set st))
       (all-points-correct (st-set st) (st-points st))))

;; ---------------------------------------------------------------------
;; Proof.  The table is hidden from the prover: nothing below depends on
;; which routes exist, apart from the no-duplicate-points check.

(defthm route-points-no-duplicates
  (no-duplicatesp-eq (strip-cars (route-points r))))

(in-theory (disable known-route route-sections route-points))

;;   The interesting case is granting a route.  Its own points are
;; set by SET-POINTS.  Every other set route keeps its points because a
;; point is moved only if it is unlocked, i.e. used by no set route.

(defthm point-pos-acons
  (equal (point-pos p (cons (cons q v) al))
         (if (equal p q) v (point-pos p al))))

(in-theory (disable point-pos))

(defthm point-pos-set-points-not-member
  (implies (not (member-eq p (strip-cars need)))
           (equal (point-pos p (set-points need points))
                  (point-pos p points))))

;; Moving points that are either already in place or unlocked never
;; disturbs a requirement NEED2 drawn from the locked set.
(defthm point-pos-set-points-available
  (implies (and (points-available need points locked)
                (member-eq p locked))
           (equal (point-pos p (set-points need points))
                  (point-pos p points))))

(defthm points-correct-preserved
  (implies (and (points-correct need2 points)
                (subsetp-eq (strip-cars need2) locked)
                (points-available need points locked))
           (points-correct need2 (set-points need points))))

(defthm subsetp-append-left
  (implies (subsetp-eq a b) (subsetp-eq a (append c b))))

(defthm subsetp-append-split
  (equal (subsetp-eq (append x y) z)
         (and (subsetp-eq x z) (subsetp-eq y z))))

(defthm subsetp-eq-cons
  (implies (subsetp-eq a b) (subsetp-eq a (cons x b))))

(defthm subsetp-eq-refl (subsetp-eq a a))

(defthm subsetp-append-right
  (implies (subsetp-eq a b) (subsetp-eq a (append b c))))

(defun all-points-locked-by (routes locked)
  (if (atom routes)
      t
    (and (subsetp-eq (strip-cars (route-points (car routes))) locked)
         (all-points-locked-by (cdr routes) locked))))

(defthm all-points-locked-by-append
  (implies (all-points-locked-by routes locked)
           (all-points-locked-by routes (append x locked))))

(defthm routes-lock-their-points
  (all-points-locked-by routes (points-of routes)))

(defthm all-points-correct-preserved
  (implies (and (points-available need points locked)
                (all-points-correct routes points)
                (all-points-locked-by routes locked))
           (all-points-correct routes (set-points need points))))

(defthm points-correct-cons-other
  (implies (not (member-eq q (strip-cars need)))
           (equal (points-correct need (cons (cons q v) al))
                  (points-correct need al))))

(defthm points-correct-set-points-dups
  ;; after setting NEED, every requirement in NEED holds (a route must
  ;; not list the same point twice; the next theorem checks the table)
  (implies (no-duplicatesp-eq (strip-cars need))
           (points-correct need (set-points need points))))

;; Cancelling a route: removing it keeps the remaining routes disjoint
;; and correct.
(defthm sections-of-remove1-subset
  (subsetp-eq (sections-of (remove1-eq r routes)) (sections-of routes)))

(defthm intersectp-subset
  (implies (and (subsetp-eq b c) (not (intersectp-eq a c)))
           (not (intersectp-eq a b))))

(defthm member-remove1
  (implies (not (member-eq x routes))
           (not (member-eq x (remove1-eq r routes)))))

(defthm not-intersectp-sections-of-remove1
  (implies (not (intersectp-eq a (sections-of routes)))
           (not (intersectp-eq a (sections-of (remove1-eq r routes)))))
  :hints (("Goal" :use ((:instance intersectp-subset
                                   (b (sections-of (remove1-eq r routes)))
                                   (c (sections-of routes)))))))

(defthm disjoint-routes-remove1
  (implies (disjoint-routes routes)
           (disjoint-routes (remove1-eq r routes))))

(defthm all-points-correct-remove1
  (implies (all-points-correct routes points)
           (all-points-correct (remove1-eq r routes) points)))

(defthm step-preserves-safety
  (implies (safe st)
           (safe (step-ilk cmd st))))

(in-theory (disable step-ilk safe))

(defthm interlocking-safe
  (implies (safe st)
           (safe (run-ilk cmds st))))

;; The headline result: from power-up, no sequence of commands, however
;; long, strange or hostile, leads to an unsafe state.
(defthm interlocking-safe-from-init
  (safe (run-ilk cmds *init*))
  :hints (("Goal" :in-theory (enable safe))))

;; And it is not vacuous: conflicting routes really are refused, and
;; compatible ones are granted together.
(defthm interlocking-examples
  (and (equal (st-set (run-ilk '((request r1) (request r3)) *init*))
              '(r3 r1))                          ; compatible: both set
       (equal (st-set (run-ilk '((request r1) (request r4)) *init*))
              '(r1))                             ; r4 shares t2,t3: refused
       (equal (st-set (run-ilk '((occupy t5) (request r3)) *init*))
              nil)                               ; occupied track: refused
       (equal (st-set (run-ilk '((request r1) (cancel r1) (request r2))
                               *init*))
              '(r2)))                            ; p1 freed, then moved
  :rule-classes nil)
